-- Prove2me | Theorems.Thm_SamplingLLL_Supplement_theorem_5_3
-- name    : SamplingLLL.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:59:23.298813+00:00
-- url     : https://prove2.me/theorems/d1e8d159-60cb-4fab-bbb9-8f8dcf153a93
-- title:
--   Theorem 5.3, p.16 — Exposure Lemma: FPRAS and perfect sampler under (X1)–(X4)
-- statement:
--   Let an atomic product-space CSP have $\lambda(a)>0$ for every $a\in A$. Let rationals $\kappa\in(0,1)$, $\beta>0$, $K,R\in(0,1]$, $\rho\in(0,1)$ and $y_a\in(0,1)$ for $a\in A$ be given, and put $F=(1-\kappa)^{-1}$, $\ell=\log F$, $Y_v(b)=\prod_{e\in\Gamma_v(b)}(1-y_e)^{-1}$, $k_{\max}=\max_a k_a$,
--   $$
--   B^*=\max_{a\in A}\beta\lambda(a)F^{k_a},\qquad\eta=\max_{b\in A,\ v\in\mathrm{vbl}(b)}\ \sum_{e\in\Gamma_v(b)}y_e(k_e-1).
--   $$
--   Suppose $B^*<1$, $\eta<1$, and
--
--   1. (X1) load: $\sum_{a:\,v\in\mathrm{vbl}(a)}\beta\lambda(a)F^{k_a-1}\le\kappa$ for every variable $v$;
--   2. (X2) root: $\prod_{v\in\mathrm{vbl}(c)}Y_v(c)\le K\beta$ for every constraint $c$;
--   3. (X3) extension: $F^{|U|}\lambda_U(b)\prod_{v\in U}Y_v(b)\le R\,y_b$ for every exposure step $(b,U)$;
--   4. (X4) work: $2K\ell k_{\max}\le\rho(1-B^*)(1-\eta)$.
--
--   Then, for absolute constants $C$, $d$, $K_0$: $Z>0$; the sampler of Appendix C terminates almost surely with law exactly $\mu$ and expected time at most
--   $$
--   C\bigl((L+1)\,\lceil(1-\rho)^{-1}\rceil\,\lceil(1-B^*)^{-1}\rceil\bigr)^d ;
--   $$
--   and for every rational $\varepsilon\in(0,1]$ the FPRAS outputs $\hat Z$ with $(1-\varepsilon)Z\le\hat Z\le(1+\varepsilon)Z$ with probability at least $3/4$, in time at most $C((L+\ell(\varepsilon)+1)\lceil1/\varepsilon\rceil\lceil(1-\rho)^{-1}\rceil\lceil(1-B^*)^{-1}\rceil)^d$ on every run. Here $L$ is the input length, including the encodings of $\kappa,\beta,K,R,\rho$ and $y$.
--
--   The lemma charges an extension only for the product mass of the variables it newly exposes; it is the general statement behind the transversal bound of Theorem 2.13(i).
--
--   **Formalization Note** The hypotheses are the structure `ExposureHyp`; the procedures are `expSampler` and `expFpras`. $\ell=\log F$ is the real natural logarithm and occurs only in (X4).
--
--   Differences from the source:
--   - reading: "$Z$ has an FPRAS, and $\mu$ has a perfect sampler" → the clauses are stated for the explicit procedures `expSampler` and `expFpras` of Appendix C, with no existential quantifier over programs; reason: the base mission's `Proc` has no machine model, so an existential over programs would make every running-time clause vacuous; this is the convention of the published Theorem 2.6
--   - reading: "running in expected time polynomial in the input length, $(1-\rho)^{-1}$, and $(1-B^*)^{-1}$, with universal polynomial degree" → sampler: expected ticks at most $C((L+1)\lceil(1-\rho)^{-1}\rceil\lceil(1-B^*)^{-1}\rceil)^d$; FPRAS: for every rational $\varepsilon\in(0,1]$, relative error $\varepsilon$ with probability at least $3/4$ and worst-case ticks at most $C((L+\ell(\varepsilon)+1)\lceil1/\varepsilon\rceil\lceil(1-\rho)^{-1}\rceil\lceil(1-B^*)^{-1}\rceil)^d$ under the work cap of p.25, with $C$, $d$ absolute; reason: one polynomial in the product of the three quantities with one absolute degree; the FPRAS clause has its standard meaning, and a worst-case bound implies the expected one
--   - encoding: $\mu$ is assumed to exist → $Z>0$ is a stated conclusion; reason: the conditional law requires $Z>0$, which the proof establishes
--   - encoding: $B^*$, $\eta$ and $k_{\max}$ are maxima over $A$ and over pairs $(b,v)$, undefined for an empty family → the maxima are taken to be $0$ when there is nothing to maximize over; reason: all terms are nonnegative, so the values are the printed ones whenever $A\ne\emptyset$; for $A=\emptyset$ the statement is the trivial instance $Z=1$
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Definition 5.2 and Theorem 5.3, p.16; proof in Appendix C.1–C.4, pp.34–38

import Mathlib
import Definitions.Def_SamplingLLL_Supplement_expoData

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL.Supplement

open Proc

/-- Theorem 5.3 (Exposure Lemma), p.16. Let an atomic product-space CSP have `λ(a) > 0` for every `a`, and
let rationals `κ ∈ (0,1)`, `β > 0`, `K, R ∈ (0,1]`, `ρ ∈ (0,1)` and `y_a ∈ (0,1)` satisfy `B* < 1`, `η < 1`
and (X1)–(X4) (`ExposureHyp`). Then `Z > 0`; the sampler of Appendix C terminates almost surely with law
exactly `μ`, in expected time polynomial in the input length, `(1−ρ)^{-1}` and `(1−B*)^{-1}`; and for every
rational `ε ∈ (0,1]` the FPRAS of Appendix C has relative error `ε` with probability at least `3/4`, in
worst-case time polynomial in the same quantities, in the bit length of `ε` and in `1/ε`. The degree `d` is
universal.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), Theorem 5.3, p.16; proof in
Appendix C.1–C.4, pp.35–38.

**Formalization Note.** The clauses are about the explicit procedures `expSampler` and `expFpras`
(Appendix C on top of the base execution machinery), not about a program chosen by `∃`, since `Proc` has
no machine. Costs are bit costs by the base charge table. `C`, `d`, `K₀` are absolute; `K₀` and `d` enter
the FPRAS's work cap. "Expected time polynomial in the input length, `(1−ρ)^{-1}` and `(1−B*)^{-1}`" is
`C ((L+1) ⌈(1−ρ)^{-1}⌉ ⌈(1−B*)^{-1}⌉)^d`. The FPRAS bound is worst case, which implies the expected bound. -/
theorem theorem_5_3 : ∃ C d K0 : ℕ, ∀ {n m : ℕ} (I : AtomicCSP n m) (κ β K R ρ : ℚ)
    (y : Fin m → ℚ), ExposureHyp I κ β K R ρ y →
    0 < I.toCSP.Z Finset.univ ∧
    mass (expSampler I κ β K R ρ y) = 1 ∧
    (∀ x, law (expSampler I κ β K R ρ y) x =
      ENNReal.ofReal ((I.toCSP.mu Finset.univ x : ℚ) : ℝ)) ∧
    expTicks (expSampler I κ β K R ρ y) ≤
      ((C * ((expInputSize I κ β K R ρ y + 1) * expSlack I κ β ρ) ^ d : ℕ) : ℝ≥0∞) ∧
    ∀ ε : ℚ, 0 < ε → ε ≤ 1 →
      mass (expFpras I κ β K R ρ y K0 d ε) = 1 ∧
      (∀ r, expFpras I κ β K R ρ y K0 d ε r ≠ 0 →
        r.2.1 ≤ C * ((expInputSize I κ β K R ρ y + bits ε + 1) * ⌈(1 / ε : ℚ)⌉₊ *
          expSlack I κ β ρ) ^ d) ∧
      (3 / 4 : ℝ≥0∞) ≤ probOf (expFpras I κ β K R ρ y K0 d ε) fun Zh =>
        (1 - ε) * I.toCSP.Z Finset.univ ≤ Zh ∧ Zh ≤ (1 + ε) * I.toCSP.Z Finset.univ := by sorry

end SamplingLLL.Supplement
