-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_exists_restrict_twistMulBundle_1b736d316c28
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_exists_restrict_twistMulBundle_1b736d316c28
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:09:57.422497+00:00
-- url     : https://prove2.me/theorems/28e3086e-2653-48b7-8d97-5de14e0b267e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Three On W Gen exists restrict twist Mul Bundle 1b736d316c28: P2 M Ground Theory Heights  Heights Kleiman Step Three On W Gen exists restrict twist Mul
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Three On W Gen exists restrict twist Mul Bundle 1b736d316c28 construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Three On W Gen exists restrict twist Mul Bundle 1b736d316c28 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeOnWGen.lean#L92-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeOnWGen.lean#L92-L99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnWGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrictGenerated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepDataJProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSubvarDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGenerated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.StepThree GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Gen
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_exists_restrict_twistMulBundle_1b736d316c28 (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (hle : primeOf (S := S) x ≤ primeOf (S := S) y) (M : LineBundle S x) (M' : LineBundle S y)
    (r : Ω → K') (h : RestrictData M.toSubSystem hxy M'.toSubSystem r) (p : ℕ) (m : ℤ) :
    ∃ r' : Ω → K', RestrictData (twistMulBundle M p m).toSubSystem hxy
      (twistMulBundle M' p m).toSubSystem r' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepThree».«OnW».«Gen».«exists_restrict_twistMulBundle» := P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_exists_restrict_twistMulBundle_1b736d316c28
