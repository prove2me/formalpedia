-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_evalHom_apply_01d7b863b51a
-- name    : P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_evalHom_apply_01d7b863b51a
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:59.023835+00:00
-- url     : https://prove2.me/theorems/e2ad342c-507e-4b35-a78d-99b20b7d0993
-- title:
--   P2 M Ground Theory Heights  Heights Model Free Sheaf Basis eval Hom apply 01d7b863b51a: P2 M Ground Theory Heights  Heights Model Free Sheaf Basis eval Hom apply 01d7b863b51a
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Free Sheaf Basis eval Hom apply 01d7b863b51a construction uses the P2 M Ground Theory Heights  Heights Model Free Sheaf Basis eval Hom apply 01d7b863b51a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PFreeSheafBasis.lean#L60-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PFreeSheafBasis.lean#L60-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsFreeSheafBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PFreeSheafBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Model.FreeSheafBasis
variable (Y : Scheme.{u}) (n : ℕ)
variable {Y}

theorem P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_evalHom_apply_01d7b863b51a {M N : Y.Modules} (V : Y.Opens) (x : Γ(M, V)) (φ : M ⟶ N) :
    evalHom V x φ = (φ.app V).hom x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«FreeSheafBasis».«evalHom_apply» := P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_evalHom_apply_01d7b863b51a
