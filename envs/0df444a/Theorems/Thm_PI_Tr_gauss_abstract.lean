-- Prove2me | Theorems.Thm_PI_Tr_gauss_abstract
-- name    : PI.Tr.gauss_abstract
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:28:53.773815+00:00
-- url     : https://prove2.me/theorems/66179f49-f49b-4993-a9e0-5e39f0c7d93b
-- title:
--   Tr: gauss abstract
-- statement:
--   The Tr construction uses the gauss abstract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeTransference/GaussAbs.lean#L21-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeTransference/GaussAbs.lean#L21-L140

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_GaussAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Real
open PI PI.Tr

theorem PI.Tr.gauss_abstract {X Y : Type} (a a0 : X → ℝ) (q θ : Y → ℝ) (n c : ℝ)
    (hq : ∀ y, 0 ≤ q y) (ha0 : ∀ x, 0 ≤ a0 x) (hθ : ∀ y, |θ y| ≤ 1) (hc : 0 < c) (y0 : Y)
    (sA : ∀ t : ℝ, 0 < t → Summable fun x => Real.exp (-π * t * a x))
    (compactWordAction : ∀ t : ℝ, 0 < t → Summable fun x => Real.exp (-π * t * a0 x))
    (sQ : ∀ t : ℝ, 0 < t → Summable fun y => Real.exp (-π * q y / t))
    (Pu : ∀ t : ℝ, 0 < t → ∑' x, Real.exp (-π * t * a x) =
      c * t ^ (-n / 2) * ∑' y, Real.exp (-π * q y / t) * θ y)
    (P0 : ∀ t : ℝ, 0 < t → ∑' x, Real.exp (-π * t * a0 x) =
      c * t ^ (-n / 2) * ∑' y, Real.exp (-π * q y / t))
    (R2 l2 : ℝ) (hR : ∀ x, R2 ≤ a x) (hl : ∀ y, q y < l2 → θ y = 1)
    (s τ₁ τ₂ : ℝ) (hs : 0 < s) (h1 : 0 < τ₁) (h1' : τ₁ ≤ 1) (h2 : 0 < τ₂) (h2' : τ₂ ≤ 1) :
    1 ≤ Real.exp (-π * s * (1 - τ₁) * R2) * τ₁ ^ (-n / 2) +
      2 * (Real.exp (-π * (1 - τ₂) * l2 / s) * τ₂ ^ (-n / 2)) := by sorry
