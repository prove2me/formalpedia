-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DehomogOrd_ord_X_pow_mul_C_f5945d70f93b
-- name    : P2M_GroundTheory_Heights__Heights_DehomogOrd_ord_X_pow_mul_C_f5945d70f93b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:17:14.813233+00:00
-- url     : https://prove2.me/theorems/b8f3e917-f378-5425-be54-ce6ab44ecef5
-- title:
--   P2 M Ground Theory Heights  Heights Dehomog Ord ord X pow mul C f5945d70f93b: P2 M Ground Theory Heights  Heights Dehomog Ord ord X pow mul C f5945d70f93b
-- statement:
--   The P2 M Ground Theory Heights  Heights Dehomog Ord ord X pow mul C f5945d70f93b construction uses the P2 M Ground Theory Heights  Heights Dehomog Ord ord X pow mul C f5945d70f93b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PDehomogOrd.lean#L58-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PDehomogOrd.lean#L58-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PDehomogOrd
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
open GroundTheory.Heights₂.Heights.DehomogOrd

theorem P2M_GroundTheory_Heights__Heights_DehomogOrd_ord_X_pow_mul_C_f5945d70f93b (h₁ : OrdPolynomialLocalization.Statement) {Q : Type} [CommRing Q] (p : Ideal Q)
    [p.IsPrime] [(Ideal.map (C : Q →+* MvPolynomial Unit Q) p).IsPrime] (q : Q) (d : ℕ) :
    Ring.ord (Localization.AtPrime (Ideal.map (C : Q →+* MvPolynomial Unit Q) p))
        (algebraMap (MvPolynomial Unit Q) _ (X () ^ d * C q)) =
      Ring.ord (Localization.AtPrime p) (algebraMap Q _ q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DehomogOrd».«ord_X_pow_mul_C» := P2M_GroundTheory_Heights__Heights_DehomogOrd_ord_X_pow_mul_C_f5945d70f93b
