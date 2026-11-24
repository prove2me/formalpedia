-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_res_res_ee0c529cdd77
-- name    : P2M_GroundTheory_Heights__Heights_Model_res_res_ee0c529cdd77
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:48.426345+00:00
-- url     : https://prove2.me/theorems/3c2e9029-203c-4975-b91e-4a9ab8a43fba
-- title:
--   P2 M Ground Theory Heights  Heights Model res res ee0c529cdd77: P2 M Ground Theory Heights  Heights Model res res ee0c529cdd77
-- statement:
--   The P2 M Ground Theory Heights  Heights Model res res ee0c529cdd77 construction uses the P2 M Ground Theory Heights  Heights Model res res ee0c529cdd77 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PClearDenominators.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PClearDenominators.lean#L17-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PullbackBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_RatLocalAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
variable {X : Scheme.{0}} (M : X.Modules)

theorem P2M_GroundTheory_Heights__Heights_Model_res_res_ee0c529cdd77 {A B C : X.Opens} (i : A ⟶ B) (j : B ⟶ C) (k : A ⟶ C) (x : Γ(M, C)) :
    (M.presheaf.map i.op).hom ((M.presheaf.map j.op).hom x) = (M.presheaf.map k.op).hom x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«res_res» := P2M_GroundTheory_Heights__Heights_Model_res_res_ee0c529cdd77
