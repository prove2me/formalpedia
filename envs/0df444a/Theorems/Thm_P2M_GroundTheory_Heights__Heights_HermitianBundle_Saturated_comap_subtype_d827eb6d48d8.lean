-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_Saturated_comap_subtype_d827eb6d48d8
-- name    : P2M_GroundTheory_Heights__Heights_HermitianBundle_Saturated_comap_subtype_d827eb6d48d8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:34.125895+00:00
-- url     : https://prove2.me/theorems/706a2eaa-5976-4858-b19d-3f317dc176fc
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Bundle Saturated comap subtype d827eb6d48d8: P2 M Ground Theory Heights  Heights Hermitian Bundle Saturated comap subtype d827eb6d48d8
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Bundle Saturated comap subtype d827eb6d48d8 construction uses the P2 M Ground Theory Heights  Heights Hermitian Bundle Saturated comap subtype d827eb6d48d8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsBundles.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsBundles.lean#L23-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsBundles
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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Heights₂.Heights.HermitianBundle

theorem P2M_GroundTheory_Heights__Heights_HermitianBundle_Saturated_comap_subtype_d827eb6d48d8 {M : HermitianBundle K} {G : Submodule (𝓞 K) M.carrier}
    (hG : M.Saturated G) (F : Submodule (𝓞 K) M.carrier) :
    (M.sub F).Saturated (G.comap F.subtype) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianBundle».«Saturated».«comap_subtype» := P2M_GroundTheory_Heights__Heights_HermitianBundle_Saturated_comap_subtype_d827eb6d48d8
