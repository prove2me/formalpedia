-- Prove2me | Theorems.Thm_Rigidity
-- name    : Rigidity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:27:47.286866+00:00
-- url     : https://prove2.me/theorems/9ba73124-abba-4072-b0ba-53f0ebc2af38
-- title:
--   Rigidity: Rigidity
-- statement:
--   Vanishing of the higher derivatives at a critical point (paper lem:rigidity).
--   If `u` is `p`-harmonic on `Ω` with its classical gradient as weak gradient, is `C^m`
--   there, and has a critical point at `x₀ ∈ Ω`, then every diagonal evaluation
--   `iteratedFDeriv ℝ j u x₀ (fun _ => w)` vanishes for `2 ≤ j ≤ m`.
--
--   The order `m` is FREE: it is a bound variable of this lemma, not the ambient `k` of
--   the main estimate, because the decay lemma applies it at orders it chooses.  The
--   conclusion is DIAGONAL, which is all that the rigidity input can deliver and all
--   that the consumers use.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/Rigidity.lean#L16-L214
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/Rigidity.lean#L16-L214

import Definitions.Def_PHigherOrder_BlowupUniformConvergence
import Definitions.Def_PHigherOrder_PHarmGradientCompactness
import Definitions.Def_PHigherOrder_PHarmUnionExhaustion
import Definitions.Def_PHigherOrder_PHarmLimit
import Definitions.Def_PHigherOrder_LewisRigidityInput
import Definitions.Def_PHigherOrder_Rigidity
import Theorems.Thm_BlowupUniformConvergence
import Theorems.Thm_PHarmGradientCompactness
import Theorems.Thm_PHarmLimit
import Theorems.Thm_PHarmUnionExhaustion

set_option autoImplicit false

theorem Rigidity (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hL : LewisRigidityInput p) (F : FirstOrderEstimateInput p)
    (Ω : Set Plane) (u : Plane → ℝ) (x₀ : Plane) (hx₀ : x₀ ∈ Ω)
    (m : ℕ) (hm : 2 ≤ m)
    (hu : ContDiffOn ℝ (m : ℕ∞) u Ω)
    (hph : IsPHarm p Ω u (gradient u))
    (hcrit : gradient u x₀ = 0) :
    ∀ j, 2 ≤ j → j ≤ m → ∀ w : Plane, iteratedFDeriv ℝ j u x₀ (fun _ => w) = 0 := by sorry
