-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIncOrd_ord_atPrime_ringEquiv_765759cdd22c
-- name    : P2M_GroundTheory_Heights__Heights_ChartIncOrd_ord_atPrime_ringEquiv_765759cdd22c
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:03.750344+00:00
-- url     : https://prove2.me/theorems/a31241c5-0ce9-40dd-ad9e-4bd2f1d70cf2
-- title:
--   P2 M Ground Theory Heights  Heights Chart Inc Ord ord at Prime ring Equiv 765759cdd22c: P2 M Ground Theory Heights  Heights Chart Inc Ord ord at Prime ring Equiv 765759cdd22c
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Inc Ord ord at Prime ring Equiv 765759cdd22c construction uses the P2 M Ground Theory Heights  Heights Chart Inc Ord ord at Prime ring Equiv 765759cdd22c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartIncOrd.lean#L169-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartIncOrd.lean#L169-L174

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartIncOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartIncOrd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIncOrd
variable {F : Type} [Field F] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)

theorem P2M_GroundTheory_Heights__Heights_ChartIncOrd_ord_atPrime_ringEquiv_765759cdd22c {R S : Type*} [CommRing R] [CommRing S] (f : R ≃+* S) (P : Ideal R) [P.IsPrime]
    (P' : Ideal S) [P'.IsPrime] (h : P = P'.comap f) (x : R) :
    Ring.ord (Localization.AtPrime P') (algebraMap S _ (f x)) =
      Ring.ord (Localization.AtPrime P) (algebraMap R _ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIncOrd».«ord_atPrime_ringEquiv» := P2M_GroundTheory_Heights__Heights_ChartIncOrd_ord_atPrime_ringEquiv_765759cdd22c
