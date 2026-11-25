-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HeightOfCycle_finsum_log_gaussNorm_prod_bff67275f7cc
-- name    : P2M_GroundTheory_Heights__Heights_HeightOfCycle_finsum_log_gaussNorm_prod_bff67275f7cc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:19:24.10397+00:00
-- url     : https://prove2.me/theorems/ef7b8881-e82a-43b9-8da3-ecde24db7647
-- title:
--   P2 M Ground Theory Heights  Heights Height Of Cycle finsum log gauss Norm prod bff67275f7cc: P2 M Ground Theory Heights  Heights Height Of Cycle finsum log gauss Norm prod bff67275f7cc
-- statement:
--   The P2 M Ground Theory Heights  Heights Height Of Cycle finsum log gauss Norm prod bff67275f7cc construction uses the P2 M Ground Theory Heights  Heights Height Of Cycle finsum log gauss Norm prod bff67275f7cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHeightOfCycle.lean#L59-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHeightOfCycle.lean#L59-L71

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

theorem P2M_GroundTheory_Heights__Heights_HeightOfCycle_finsum_log_gaussNorm_prod_bff67275f7cc {ι α : Type*} (s : Finset α) (L : α → MvPolynomial ι K)
    (hL : ∀ q, L q ≠ 0) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v (∏ q ∈ s, L q)) =
      ∑ q ∈ s, ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v (L q)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HeightOfCycle».«finsum_log_gaussNorm_prod» := P2M_GroundTheory_Heights__Heights_HeightOfCycle_finsum_log_gaussNorm_prod_bff67275f7cc
