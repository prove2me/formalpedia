-- Prove2me | Theorems.Thm_STOC2027BoolCSP_Approximation_Supplement_lemma_12_1
-- name    : STOC2027BoolCSP.Approximation.Supplement.lemma_12_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:35:14.058411+00:00
-- url     : https://prove2.me/theorems/ec35ad0c-bac2-4f74-b3d6-5246a6d35109
-- title:
--   Lemma 12.1 — Fock product estimate $\|UV\|_u\le\|U\|_{pu}\|V\|_{qu}$ and $\|U^h\|_u\le\|U\|_{hu}^h$
-- statement:
--   Let $U,V$ be formal power series in $N$ variables with real or complex coefficients, and for $u\ge 0$ let
--   $$\|U\|_u^2=\sum_{\alpha\in\mathbb N^N}\alpha!\,u^{|\alpha|}\,\big|[z^\alpha]U\big|^2\in[0,\infty].$$
--   Then for all $p,q>1$ with $p^{-1}+q^{-1}=1$,
--   $$\|UV\|_u\le\|U\|_{pu}\,\|V\|_{qu},$$
--   and for every integer $h\ge1$,
--   $$\|U^h\|_u\le\|U\|_{hu}^{\,h}.$$
--   Both inequalities hold in $[0,\infty]$, in particular trivially when the right side is infinite.
--
--   The estimate bounds every higher term of the two-hub expansion (57) in the proof of Theorem 12.2, through (53).
--
--   Differences from the source:
--   - encoding: power series U, V with norms used when finite (Tonelli remark in the proof) → MvPowerSeries over any RCLike field (ℝ or ℂ); norms valued in [0, ∞]; reason: the same series and norms; the [0, ∞] values make the divergent case explicit
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 25 (PDF 28), Lemma 12.1, with the norms of §12.1 (printed p. 24)

import Mathlib
import Definitions.Def_STOC2027BoolCSP_Approximation_Supplement_Fock

namespace STOC2027BoolCSP.Approximation.Supplement

open scoped ENNReal

/-- Lemma 12.1 (Fock product estimate), printed p. 25. For formal power series `U, V` in `N`
variables with real or complex coefficients and a scale `u ≥ 0`: for conjugate exponents
`p, q > 1`, `1/p + 1/q = 1`, `‖UV‖_u ≤ ‖U‖_{pu} ‖V‖_{qu}`; and `‖U^h‖_u ≤ ‖U‖_{hu}^h` for every
integer `h ≥ 1`. The norms take values in `[0, ∞]`. -/
theorem lemma_12_1 {𝕜 : Type*} [RCLike 𝕜] (N : ℕ) (U V : MvPowerSeries (Fin N) 𝕜) (u : ℝ)
    (hu : 0 ≤ u) :
    (∀ p q : ℝ, 1 < p → 1 < q → p⁻¹ + q⁻¹ = 1 →
        fockNorm (U * V) u ≤ fockNorm U (p * u) * fockNorm V (q * u)) ∧
    (∀ h : ℕ, 1 ≤ h → fockNorm (U ^ h) u ≤ fockNorm U ((h : ℝ) * u) ^ h) := by sorry

end STOC2027BoolCSP.Approximation.Supplement
