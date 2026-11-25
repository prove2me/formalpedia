-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_primeOf_le_zeroIdeal_c79a644ed284
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_primeOf_le_zeroIdeal_c79a644ed284
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:58:12.140075+00:00
-- url     : https://prove2.me/theorems/1dcbd716-0f0e-46f6-ad79-bcdaacd06f2f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Three On W Gen prime Of le zero Ideal c79a644ed284: P2 M Ground Theory Heights  Heights Kleiman Step Three On W Gen prime Of le zero Ideal c79a644ed284
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Three On W Gen prime Of le zero Ideal c79a644ed284 construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Three On W Gen prime Of le zero Ideal c79a644ed284 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeOnWGen.lean#L39-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeOnWGen.lean#L39-L46

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_primeOf_le_zeroIdeal_c79a644ed284 (D : SubSystem S x Ω) (s : Ω) : primeOf (S := S) x ≤ zeroIdeal D s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepThree».«OnW».«Gen».«primeOf_le_zeroIdeal» := P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_primeOf_le_zeroIdeal_c79a644ed284
