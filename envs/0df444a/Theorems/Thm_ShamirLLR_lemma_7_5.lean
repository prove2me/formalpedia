-- Prove2me | Theorems.Thm_ShamirLLR_lemma_7_5
-- name    : ShamirLLR.lemma_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:27:26.381298+00:00
-- url     : https://prove2.me/theorems/593a6518-fe24-46f6-a5af-9376cc848fc5
-- title:
--   Lemma 7.5 — Fourier weights of a probability map
-- statement:
--   Let $p$ be an odd prime, $E$ a finite $\mathbb F_p$-vector space and $A:E\to[0,1]$, with weights $\mu(0)=1$, $\mu(\gamma)=2|\widehat A(\gamma)|$ for $\gamma\neq0$. Then
--   $$
--   \sum_{\gamma\in E^*}\mu(\gamma)^2\le2,\qquad \mu(\gamma)\le\sigma=2^{-1/2}\quad(\gamma\neq0).
--   $$
--   If moreover $E\subseteq\mathbb F_p^d$ with $d\le D$ and $A(v)=A_T(\vartheta+v/p)$ for a trigonometric polynomial $A_T$ on $\mathbb T^d$ with Fourier support in $[-T,T]^d$ (and values in $[0,1]$ there), then the support of $\mu$ has at most $(2T+1)^D$ elements.
--
--   These bounds feed the two-information-set summation of Lemma 7.6.
--
--   Differences from the source:
--   - generalization: the readouts $A^*_i(v)=A_i(\vartheta_i+v/p)$ on $E_i=\mathrm{span}(\beta_{i,1},\beta_{i,2})$ of Eq. (56) → the two bounds for every $A:E\to[0,1]$ on every finite $\mathbb F_p$-space; the support bound for every subspace $E\subseteq\mathbb F_p^d$, $d\le D$; reason: the proof uses only $0\le A\le1$ and Eq. (57); the source's readouts are instances
--   - encoding: sums over $E^*$; trigonometric polynomial → a `Fintype` instance on $E^*$; a continuous function with Fourier support in $[-T,T]^d$; reason: the instance only lets the sum be written; continuity plus finite Fourier support is a trigonometric polynomial
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), Lemma 7.5, Eq. (59), p.55, with Eq. (56)–(58), pp.54–55 (PDF pp.55–56)

import Mathlib
import Definitions.Def_ShamirLLR_finFourier
import Definitions.Def_ShamirLLR_torus

set_option autoImplicit false

namespace ShamirLLR

open Classical in
/-- **Lemma 7.5 (Fourier weights of a probability map).** The weights `μ(0) = 1`,
`μ(γ) = 2|Â(γ)|` (`γ ≠ 0`) of Eq. (58) of a map `A : E → [0, 1]` on a finite `𝔽_p`-space satisfy
`∑_γ μ(γ)² ≤ 2` and `μ(γ) ≤ σ = 2^{−1/2}` for `γ ≠ 0` (Eq. (59)). If `E ⊆ 𝔽_p^d`, `d ≤ D`, and
`A(v) = A_T(ϑ + v/p)` for a trigonometric polynomial `A_T` on `𝕋^d` with Fourier support in
`[−T, T]^d` (Eq. (57)), the support of `μ` has size at most `(2T + 1)^D`.

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
Lemma 7.5, Eq. (59), p.55, with Eq. (56)–(58), pp.54–55.

**Formalization Note.** The source states the lemma for the readouts `A*_i` of Eq. (56) on
`E_i = span(β_{i,1}, β_{i,2})`; here the first two bounds are for every `A : E → [0, 1]` and the
support bound for every subspace `E ⊆ 𝔽_p^d`. A trigonometric polynomial is a continuous
function with finite Fourier support. The `Fintype` instance on `E^*` only lets the sum be
written. -/
theorem lemma_7_5 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (∀ {E : Type} [AddCommGroup E] [Module (ZMod p) E] [Fintype E]
        [Fintype (Module.Dual (ZMod p) E)] (A : E → ℝ), (∀ v, 0 ≤ A v ∧ A v ≤ 1) →
        (∑ γ : Module.Dual (ZMod p) E, fourierWeight A γ ^ 2 ≤ 2) ∧
          ∀ γ : Module.Dual (ZMod p) E, γ ≠ 0 → fourierWeight A γ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      ∀ (D d T : ℕ), d ≤ D → ∀ (E : Submodule (ZMod p) (Fin d → ZMod p))
        [Fintype (Module.Dual (ZMod p) E)] (AT : Torus d → ℝ) (ϑ : Torus d),
        Continuous AT → FourierSuppIn AT T →
        (∀ v : E, 0 ≤ AT (ϑ + fpToTorus p (v : Fin d → ZMod p)) ∧
          AT (ϑ + fpToTorus p (v : Fin d → ZMod p)) ≤ 1) →
        ((Finset.univ : Finset (Module.Dual (ZMod p) E)).filter (fun γ =>
            fourierWeight (fun v : E => AT (ϑ + fpToTorus p (v : Fin d → ZMod p))) γ ≠ 0)).card ≤
          (2 * T + 1) ^ D := by sorry

end ShamirLLR
