-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_tstar_norm_sq
-- name    : ReciprocityTheory.L2DbarEstimates.E.tstar_norm_sq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:56:35.558605+00:00
-- url     : https://prove2.me/theorems/fa73fcc5-596f-4b9f-a85a-ed3a377155f0
-- title:
--   E: tstar norm sq
-- statement:
--   The E construction uses the tstar norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/TstarNormSq.lean#L117-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/TstarNormSq.lean#L117-L145

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_TstarNormSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.E
open MeasureTheory
open scoped ComplexConjugate
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.E.tstar_norm_sq (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n)
    (hz : IsLocalHomeomorph z) (ph ψ : M → ℝ) (f : M → V n) (hph : CkR n z 1 ph)
    (hψ : CkR n z 1 ψ) (hf : ∀ j, Ck n z 1 (fun x => f x j)) (x : M) :
    ‖tstar n z (fun y => ph y - 2 * ψ y) (fun y => ph y - ψ y) f x‖ ^ 2 *
        Real.exp (-(ph x - 2 * ψ x)) =
      ‖∑ j, (dTw n z ph j (fun y => f y j) x + f x j * d n z j (fun y => (ψ y : ℂ)) x)‖ ^ 2 *
        Real.exp (-ph x) := by sorry
