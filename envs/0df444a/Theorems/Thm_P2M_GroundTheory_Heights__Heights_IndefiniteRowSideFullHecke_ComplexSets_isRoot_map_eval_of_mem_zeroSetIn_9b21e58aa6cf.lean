-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isRoot_map_eval_of_mem_zeroSetIn_9b21e58aa6cf
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isRoot_map_eval_of_mem_zeroSetIn_9b21e58aa6cf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:50.866196+00:00
-- url     : https://prove2.me/theorems/525155d3-d1d2-4a29-add1-2fca84cf0140
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets is Root map eval of mem zero Set In 9b21e58aa6cf: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Com
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets is Root map eval of mem zero Set In 9b21e58aa6cf construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets is Root map eval of mem zero Set In 9b21e58aa6cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalModelProper.lean#L9-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalModelProper.lean#L9-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelProper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isRoot_map_eval_of_mem_zeroSetIn_9b21e58aa6cf {n m : ℕ} {I : Ideal (MvPolynomial (Fin n ⊕ Fin m) ℂ)}
    {w : Fin n ⊕ Fin m → ℂ} (hw : w ∈ zeroSetIn I) (i : Fin m) (P : Polynomial (MvPolynomial (Fin n) ℂ))
    (hP : P.eval₂ (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin m) ℂ).toRingHom
      (X (Sum.inr i)) ∈ I) :
    (P.map (eval (firstCoords w))).IsRoot (w (Sum.inr i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«isRoot_map_eval_of_mem_zeroSetIn» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isRoot_map_eval_of_mem_zeroSetIn_9b21e58aa6cf
