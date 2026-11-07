-- Prove2me | Theorems.Thm_SamplingLLL_theorem_5_1
-- name    : SamplingLLL.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:58:58.328233+00:00
-- url     : https://prove2.me/theorems/d454bf9c-ec69-4ab3-a8cc-10dabf2cf987
-- title:
--   Theorem 5.1, p.15 — Execution Theorem, with its time and FPRAS clauses made explicit
-- statement:
--   Let every reachable insertion task have a finite separated membership search, a budget $B_i\in(0,1)$, domination masses $\bar a_t\ge a_t$, an executable proposal with $q_i(t)>0$ whenever $\bar a_t>0$, the exact local operation, and
--   $$
--   \bar a_t\le B_iq_i(t)\prod_{j\in C_t}s_j. \tag{D}
--   $$
--   Then $Z(S),Z(S\cup\{c\})>0$, $r_{S,c}\le B_i$, the insertion and deletion kernels are exact from their declared source laws $\mu_S$, $\mu_{S\cup\{c\}}$ (so they terminate almost surely there), the signed experiment is unbiased for $r_{S,c}$, the reciprocal coin has bias $s_i/(1-r_i)$, and sequential insertion samples exactly from $\mu$. If in addition $h_i>0$ and $\rho<1$ satisfy
--   $$
--   \frac2{s_i}\sum_tq_i(t)L_i(t)R_i(t)\le\rho, \tag{W}
--   $$
--   then the expected $h$-weighted occupation of a root of each kind is at most $h_i/(1-\rho)$. If further $W\ge1$ bounds the primitives, $H_r$ bounds the ratios of $h$, and $S_{\mathrm{inv}}$ bounds $(1-B_i)^{-1}$, then with absolute $C,d$ and $\mathrm{Base}=(m+1)H_r(1-\rho)^{-1}S_{\mathrm{inv}}W$, the sampler has expected ticks at most $C\,\mathrm{Base}^d$, and for rational $\varepsilon\in(0,1]$ the FPRAS capped at any $T\ge C(\mathrm{Base}\,(\mathrm{bits}(\varepsilon)+1)\lceil1/\varepsilon\rceil)^d$ has relative error $\varepsilon$ with probability at least $3/4$.
--
--   This is the general theorem from which Theorem 2.6 follows; it uses no partition-function value.
--
--   Differences from the source:
--   - reading: "uniformly polynomial expected time" of the primitives, with polynomially bounded $\max h/\min h$, $\max(1-B)^{-1}$, $(1-\rho)^{-1}$, implying polynomial time → an explicit bound $C\,\mathrm{Base}^d$ with absolute $C,d$, in terms of a bound $W$ on the primitives (`PrimitiveBound`); reason: the quantitative form of the implication, which gives the printed one on substituting polynomial bounds
--   - reading: "FPRAS" → for every rational $\varepsilon\in(0,1]$ and every cap $T$ above an explicit polynomial: mass one and success probability at least $3/4$; the error is $\varepsilon$; reason: the proof, p.25, caps the work at eight times its expected bound and has error $\varepsilon/2$; the printed FPRAS meaning is $\varepsilon$
--   - encoding: $h$-weighted occupation "after rescaling $h$ so that $\min_j h_j=1$" → no rescaling, since both sides are homogeneous in $h$; $h$ defined and positive on all task pairs, $W$ on every reachable one; reason: tasks outside the reachable set contribute nothing to the occupation
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Theorem 5.1, p.15, and its proof, pp.24–25

import Mathlib
import Definitions.Def_SamplingLLL_ExecAnalysis

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL

open Proc

/-- Theorem 5.1 (Execution Theorem), p.15. Under the standing hypotheses and (D) on every reachable task:
exact insertion and deletion kernels at every level at least the target size, with almost-sure termination
from the declared source laws; the bound `r_i ≤ B_i`; bounded unbiased signed estimators; reciprocal coins;
and an exact sampler by sequential insertion. Under (W), the `h`-weighted occupation from a root of each
kind is at most `h_i/(1-ρ)`. Under a bound `W` on the primitives, explicit polynomial bounds on the time of
the sampler and of the FPRAS.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), Theorem 5.1, p.15, and its proof,
pp.24–25.

**Formalization Note.** "Uniformly polynomial expected time" is replaced by the explicit implication: `C`
and `d` are absolute, and the bounds are `C·Base^d` with `Base = (m+1)·Hr·(1-ρ)⁻¹·Sinv·W`, where `Hr` bounds
`max h / min h`, `Sinv` bounds `max (1-B)⁻¹`, and `W` is as in `PrimitiveBound`. This is the paper's
implication made quantitative. The weighted bound is stated without rescaling `h`, since both sides are
homogeneous in `h`; types are task pairs, and `typeWeight j` makes the call counter count type `j`, across
insertion, deletion and coin invocations. -/
theorem theorem_5_1 : ∃ C d : ℕ, ∀ {n m : ℕ} (P : ProductCSP n m) (D : ExecData P)
    (abar : Finset (Fin m) → Fin m → Leaf m → ℝ),
    (∀ S c, D.Reachable S c → D.TaskOK abar S c) →
    -- exact kernels, estimators and coins (D)
    (∀ S c, D.Reachable S c →
      0 < P.Z S ∧ 0 < P.Z (insert c S) ∧
      ((P.viol S c : ℚ) : ℝ) ≤ (D.budget S c : ℝ) ∧
      ∀ (cw : Finset (Fin m) → Fin m → ℕ) (k : ℕ), (insert c S).card ≤ k →
        (∀ y, push (fun x => ((P.mu S x : ℚ) : ℝ)) ((D.level cw k).insert S c) y =
          ENNReal.ofReal ((P.mu (insert c S) y : ℚ) : ℝ)) ∧
        (∀ y, push (fun x => ((P.mu (insert c S) x : ℚ) : ℝ)) ((D.level cw k).delete S c) y =
          ENNReal.ofReal ((P.mu S y : ℚ) : ℝ)) ∧
        (D.budget S c : ℝ) * ExecData.signedMass (D.experiment (D.level cw (k - 1)) S c) =
          ((P.viol S c : ℚ) : ℝ) ∧
        mass ((D.level cw k).coin S c) = 1 ∧
        law ((D.level cw k).coin S c) true =
          ENNReal.ofReal (D.s S c / (1 - ((P.viol S c : ℚ) : ℝ)))) ∧
    (0 < P.Z Finset.univ ∧ mass D.sampler = 1 ∧
      ∀ y, law D.sampler y = ENNReal.ofReal ((P.mu Finset.univ y : ℚ) : ℝ)) ∧
    -- finite occupation (W), and time
    ∀ (h : Finset (Fin m) × Fin m → ℝ) (ρ : ℝ), (∀ i, 0 < h i) → ρ < 1 →
      (∀ S c, D.Reachable S c → D.WeightCond abar h ρ S c) →
      (∀ S c, D.Reachable S c → ∀ k, (insert c S).card ≤ k →
        (∑ j : Finset (Fin m) × Fin m, ENNReal.ofReal (h j) *
            ∑ x, ENNReal.ofReal ((P.mu S x : ℚ) : ℝ) *
              expCalls ((D.level (ExecData.typeWeight j) k).insert S c x)) ≤
          ENNReal.ofReal (h (S, c) / (1 - ρ)) ∧
        (∑ j : Finset (Fin m) × Fin m, ENNReal.ofReal (h j) *
            ∑ x, ENNReal.ofReal ((P.mu (insert c S) x : ℚ) : ℝ) *
              expCalls ((D.level (ExecData.typeWeight j) k).delete S c x)) ≤
          ENNReal.ofReal (h (S, c) / (1 - ρ)) ∧
        (∑ j : Finset (Fin m) × Fin m, ENNReal.ofReal (h j) *
            expCalls ((D.level (ExecData.typeWeight j) k).coin S c)) ≤
          ENNReal.ofReal (h (S, c) / (1 - ρ))) ∧
      ∀ (Hr Sinv W : ℝ), 1 ≤ W → D.PrimitiveBound W → (∀ i j, h i ≤ Hr * h j) →
        (∀ S c, D.Reachable S c → (D.s S c)⁻¹ ≤ Sinv) →
        let Base : ℝ := ((m : ℝ) + 1) * Hr * (1 - ρ)⁻¹ * Sinv * W
        expTicks D.sampler ≤ ENNReal.ofReal ((C : ℝ) * Base ^ d) ∧
        ∀ (ε : ℚ) (T : ℕ), 0 < ε → ε ≤ 1 →
          (C : ℝ) * (Base * ((bits ε : ℝ) + 1) * (⌈(1 / ε : ℚ)⌉₊ : ℝ)) ^ d ≤ (T : ℝ) →
          mass (D.fpras T ε) = 1 ∧
          (3 / 4 : ℝ≥0∞) ≤ probOf (D.fpras T ε) fun Zh =>
            (1 - ε) * P.Z Finset.univ ≤ Zh ∧ Zh ≤ (1 + ε) * P.Z Finset.univ := by sorry

end SamplingLLL
