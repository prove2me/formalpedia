-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_wIbp_left
-- name    : ReciprocityTheory.L2DbarEstimates.E.wIbp_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:30:34.4759+00:00
-- url     : https://prove2.me/theorems/4b5c3068-ee54-454e-b687-2dcabbf29399
-- title:
--   E: w Ibp left
-- statement:
--   The E construction uses the w Ibp left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/WIbpLeft.lean#L12-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/WIbpLeft.lean#L12-L52

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_WIbpLeft
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
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

theorem ReciprocityTheory.L2DbarEstimates.E.wIbp_left (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (k : Fin n) (a b : M → ℂ) (hph : CkR n z 1 ph) (ha : Ck n z 1 a) (hb : Ck n z 1 b)
    (hc : HasCompactSupport a ∨ HasCompactSupport b) :
    (∫ x, db n z k a x * conj (b x) * (Real.exp (-ph x) : ℂ) ∂vol n z) =
      -∫ x, a x * conj (dTw n z ph k b x) * (Real.exp (-ph x) : ℂ) ∂vol n z := by sorry
