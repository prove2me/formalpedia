-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_finsum_reindex_9a25be9a211b
-- name    : P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_finsum_reindex_9a25be9a211b
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:20.59581+00:00
-- url     : https://prove2.me/theorems/a422125c-dbc6-40ef-acbd-784033973cdb
-- title:
--   P2 M Ground Theory Heights  Heights Length Finite Algebra finsum reindex 9a25be9a211b: P2 M Ground Theory Heights  Heights Length Finite Algebra finsum reindex 9a25be9a211b
-- statement:
--   The P2 M Ground Theory Heights  Heights Length Finite Algebra finsum reindex 9a25be9a211b construction uses the P2 M Ground Theory Heights  Heights Length Finite Algebra finsum reindex 9a25be9a211b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PLengthFiniteAlgebra.lean#L124-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PLengthFiniteAlgebra.lean#L124-L158

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLengthFiniteAlgebra
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
open IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.LengthFiniteAlgebra
variable {O B : Type} [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B]

theorem P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_finsum_reindex_9a25be9a211b [Module.Finite O B] (θ : B) :
    ∑ᶠ Q : MaximalSpectrum (B ⧸ Ideal.span {θ}), Module.length O (Localization.AtPrime Q.asIdeal) =
      ∑ᶠ P : MaximalSpectrum B, Module.length O (Localization.AtPrime P.asIdeal ⧸
        Ideal.span {algebraMap B (Localization.AtPrime P.asIdeal) θ}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LengthFiniteAlgebra».«finsum_reindex» := P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_finsum_reindex_9a25be9a211b
