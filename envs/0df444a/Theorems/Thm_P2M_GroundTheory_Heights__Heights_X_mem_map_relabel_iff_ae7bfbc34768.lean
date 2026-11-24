-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_X_mem_map_relabel_iff_ae7bfbc34768
-- name    : P2M_GroundTheory_Heights__Heights_X_mem_map_relabel_iff_ae7bfbc34768
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:19.965719+00:00
-- url     : https://prove2.me/theorems/c9f841d0-cd63-4c27-9597-3501ba54cccd
-- title:
--   P2 M Ground Theory Heights  Heights X mem map relabel iff ae7bfbc34768: P2 M Ground Theory Heights  Heights X mem map relabel iff ae7bfbc34768
-- statement:
--   The P2 M Ground Theory Heights  Heights X mem map relabel iff ae7bfbc34768 construction uses the P2 M Ground Theory Heights  Heights X mem map relabel iff ae7bfbc34768 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L196-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L196-L198

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
set_option linter.unusedSectionVars false
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (ε : K ≃ K') (h : ∀ k, ι k = ι' (ε k))

theorem P2M_GroundTheory_Heights__Heights_X_mem_map_relabel_iff_ae7bfbc34768 (V : Ideal (MRing ι)) (k : K) (i : ι k) :
    (X ⟨ε k, cast (h k) i⟩ : MRing ι') ∈ V.map (relabelRingEquiv ε h) ↔ (X ⟨k, i⟩ : MRing ι) ∈ V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«X_mem_map_relabel_iff» := P2M_GroundTheory_Heights__Heights_X_mem_map_relabel_iff_ae7bfbc34768
