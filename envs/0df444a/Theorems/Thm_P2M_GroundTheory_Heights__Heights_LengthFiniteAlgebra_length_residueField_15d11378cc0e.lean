-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_length_residueField_15d11378cc0e
-- name    : P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_length_residueField_15d11378cc0e
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:47.859673+00:00
-- url     : https://prove2.me/theorems/918e00d7-b5fa-44fc-b97a-f5e84c8057e5
-- title:
--   P2 M Ground Theory Heights  Heights Length Finite Algebra length residue Field 15d11378cc0e: P2 M Ground Theory Heights  Heights Length Finite Algebra length residue Field 15d11378cc0e
-- statement:
--   The P2 M Ground Theory Heights  Heights Length Finite Algebra length residue Field 15d11378cc0e construction uses the P2 M Ground Theory Heights  Heights Length Finite Algebra length residue Field 15d11378cc0e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PLengthFiniteAlgebra.lean#L66-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PLengthFiniteAlgebra.lean#L66-L72

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
omit [IsLocalRing O]

theorem P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_length_residueField_15d11378cc0e (P : Ideal B) [P.IsMaximal] :
    Module.length O (ResidueField (Localization.AtPrime P)) = Module.length O (B ⧸ P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LengthFiniteAlgebra».«length_residueField» := P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_length_residueField_15d11378cc0e
