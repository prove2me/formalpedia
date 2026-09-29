-- Prove2me | Theorems.Thm_WLight_isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le
-- name    : WLight.isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/bdd7c5e4-98a1-5f75-8656-b0f6a538fb65
-- title:
--   Cusp criterion at width N via coefficients of FΔ^M
-- statement:
--   Let $N$ be a nonzero natural number, $F\colon\mathbb H\to\mathbb C$ a function, and $M$ a natural number with $1\le M$. Assume: $F$ is holomorphic on the upper half-plane (differentiable for the standard complex-manifold charts on $\mathbb H$ and $\mathbb C$); the composite of $F$ with the section `UpperHalfPlane.ofComplex` of the inclusion $\mathbb H\to\mathbb C$ is periodic with period $N$ as a function on $\mathbb C$; and the product $F\cdot\Delta^M$ is bounded at $i\infty$, where $\Delta$ is `ModularForm.discriminant`, the discriminant form of weight $12$ on $\mathrm{SL}_2(\mathbb Z)$. The conclusion is an equivalence: $F\cdot\Delta$ tends to $0$ as $\operatorname{Im}\tau\to\infty$ if and only if the coefficient of $q_N^n$ in the width-$N$ $q$-expansion `UpperHalfPlane.qExpansion N` of $F\cdot\Delta^M$ vanishes for every $n\le N\,(M-1)$, the subtraction being truncated natural subtraction (so for $M=1$ the condition is that the constant coefficient vanish).
--
--   This is the quantitative cusp condition of the $q$-expansion argument at a cusp of width $N$: the analytic requirement that $F\Delta$ vanish at $i\infty$ is converted into the vanishing of finitely many coefficients of the width-$N$ expansion of $F\Delta^M$, using that $\Delta$ vanishes to order $N$ in the variable $q_N$. It is used in the construction of Fricke-rational transports of modular and cusp forms and in the spanning results for them by monomials in $E_4$ and $E_6$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WLight_isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le.lean

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Geometry.Manifold.Notation
import Mathlib.FieldTheory.IntermediateField.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

theorem WLight.isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le (N : ℕ) [NeZero N] {F : ℍ → ℂ} {M : ℕ}
    (hM : 1 ≤ M) (hFhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hFper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) N)
    (hFbd : IsBoundedAtImInfty (F * ModularForm.discriminant ^ M)) :
    IsZeroAtImInfty (F * ModularForm.discriminant) ↔
      ∀ n ≤ N * (M - 1),
        (UpperHalfPlane.qExpansion N (F * ModularForm.discriminant ^ M)).coeff n = 0 := by sorry
