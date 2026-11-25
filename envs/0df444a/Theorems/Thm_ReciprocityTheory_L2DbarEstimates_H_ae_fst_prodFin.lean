-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_ae_fst_prodFin
-- name    : ReciprocityTheory.L2DbarEstimates.H.ae_fst_prodFin
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:59:34.151796+00:00
-- url     : https://prove2.me/theorems/bff3c69e-c77f-545b-a8bf-3b8d895977ee
-- title:
--   H: ae fst prod Fin
-- statement:
--   The H construction uses the ae fst prod Fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/VolProdFinApply.lean#L69-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/VolProdFinApply.lean#L69-L76

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_NeedBergmanClosed
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaOps
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_NearContinuousOfSmoothR
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_OntoWithBoundTop
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_VolProdFinApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]

theorem ReciprocityTheory.L2DbarEstimates.H.ae_fst_prodFin (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) {P : M → Prop}
    (h : ∀ᵐ x ∂vol n z, P x) : ∀ᵐ q ∂vol n (fun q : M × Fin p => z q.1), P q.1 := by sorry
