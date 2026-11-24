-- Prove2me | Theorems.Thm_ValiantBorder_cutExcludesApproximateAccelerators
-- name    : ValiantBorder.cutExcludesApproximateAccelerators
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:35:07.569162+00:00
-- url     : https://prove2.me/theorems/2f0a798f-2c6d-4582-8de7-c9c6b60b81a0
-- title:
--   Scale cuts rule out small approximate accelerators
-- statement:
--   Fix a commutative ring finitely generated over the integers and weights satisfying the scale-cut property at height $16h$, where $h≥17$. For all sufficiently large $v$, any $a$ with $(1+\lfloor\log_2 v\rfloor)^{Ca}≤v$ rules out a size-$v^a$ approximate accelerator, even after passing to a nonzero coefficient algebra.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/ApproxScales.lean#L403-L468).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/ApproxScales.lean#L403-L468.

import Definitions.Def_ValiantBorder_scaleCuts
import Definitions.Def_ValiantBorder_fieldCases

theorem ValiantBorder.cutExcludesApproximateAccelerators {A : Type} [CommRing A] [Algebra.FiniteType ℤ A]
    {θ : List Bool → A} {h C₀ v₀ : ℕ} (hh : 17 ≤ h) (hc : NS1.CutHyp θ (16 * h) C₀ v₀) :
    ∃ C v₁ : ℕ, ∀ v, v₁ ≤ v → ∀ a, NS1.lg v ^ (C * a) ≤ v →
      ∀ (R : Type) [CommRing R] [Nontrivial R] [Algebra A R], ¬ NS1.HasAccA θ R (16 * h) v (v ^ a) := by sorry
