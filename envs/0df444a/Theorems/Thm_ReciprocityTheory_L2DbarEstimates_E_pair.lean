-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_pair
-- name    : ReciprocityTheory.L2DbarEstimates.E.pair
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:02:47.743026+00:00
-- url     : https://prove2.me/theorems/fede9f6b-35e3-4436-aa6d-24dea27b2392
-- title:
--   E: pair
-- statement:
--   The E construction uses the pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/ImportsTer.lean#L14-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/ImportsTer.lean#L14-L68

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_WIbpLeft
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_ImportsBis
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_ImportsTer
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj

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

theorem ReciprocityTheory.L2DbarEstimates.E.pair (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (hph : CkR n z 2 ph) (a b : M → ℂ) (ha : Ck n z 2 a) (_hac : HasCompactSupport a)
    (hb : Ck n z 2 b) (hbc : HasCompactSupport b) (j k : Fin n) :
    (∫ x, dTw n z ph j a x * conj (dTw n z ph k b x) * (Real.exp (-ph x) : ℂ) ∂vol n z) =
      (∫ x, d n z j (db n z k (fun y => (ph y : ℂ))) x * a x * conj (b x) *
          (Real.exp (-ph x) : ℂ) ∂vol n z) +
        ∫ x, db n z k a x * conj (db n z j b x) * (Real.exp (-ph x) : ℂ) ∂vol n z := by sorry
