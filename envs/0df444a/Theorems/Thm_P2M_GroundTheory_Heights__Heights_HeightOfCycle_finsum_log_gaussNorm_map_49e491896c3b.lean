-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HeightOfCycle_finsum_log_gaussNorm_map_49e491896c3b
-- name    : P2M_GroundTheory_Heights__Heights_HeightOfCycle_finsum_log_gaussNorm_map_49e491896c3b
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:19:29.477835+00:00
-- url     : https://prove2.me/theorems/9921a2fc-a4cf-5184-9d9f-3d10c43fa9b4
-- title:
--   P2 M Ground Theory Heights  Heights Height Of Cycle finsum log gauss Norm map 49e491896c3b: P2 M Ground Theory Heights  Heights Height Of Cycle finsum log gauss Norm map 49e491896c3b
-- statement:
--   The P2 M Ground Theory Heights  Heights Height Of Cycle finsum log gauss Norm map 49e491896c3b construction uses the P2 M Ground Theory Heights  Heights Height Of Cycle finsum log gauss Norm map 49e491896c3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHeightOfCycle.lean#L33-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHeightOfCycle.lean#L33-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsFibreMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHeightOfCycle
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
open MvPolynomial NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.HeightOfCycle
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_HeightOfCycle_finsum_log_gaussNorm_map_49e491896c3b {E : Type*} [Field E] [NumberField E] [Algebra E K] {ι : Type*}
    {P : MvPolynomial ι E} (hP : P ≠ 0) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v (P.map (algebraMap E K))) =
      Module.finrank E K *
        ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), Real.log (gaussNorm v P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HeightOfCycle».«finsum_log_gaussNorm_map» := P2M_GroundTheory_Heights__Heights_HeightOfCycle_finsum_log_gaussNorm_map_49e491896c3b
