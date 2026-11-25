-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecIdealOfPrime_residue_surj_a014fc5c050d
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecIdealOfPrime_residue_surj_a014fc5c050d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:43:18.278466+00:00
-- url     : https://prove2.me/theorems/3ea5947c-2a3d-4c41-8c3c-962cc85aae0e
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec Ideal Of Prime residue surj a014fc5c050d: P2 M Ground Theory Heights  Heights Vertical Sec Ideal Of Prime residue surj a014fc5c050d
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec Ideal Of Prime residue surj a014fc5c050d construction uses the P2 M Ground Theory Heights  Heights Vertical Sec Ideal Of Prime residue surj a014fc5c050d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecIdealOfPrime.lean#L95-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecIdealOfPrime.lean#L95-L105

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecIdealOfPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsGenSecKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecIdealOfPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecIdealOfPrime

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecIdealOfPrime_residue_surj_a014fc5c050d {K : Type*} [Field K] [NumberField K] (e n : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (z : (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField) :
    ∃ a b, z = eval₂Hom (resToKappa e n v) (parYκ e n v) a / eval₂Hom (resToKappa e n v) (parYκ e n v) b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecIdealOfPrime».«residue_surj» := P2M_GroundTheory_Heights__Heights_Vertical_SecIdealOfPrime_residue_surj_a014fc5c050d
