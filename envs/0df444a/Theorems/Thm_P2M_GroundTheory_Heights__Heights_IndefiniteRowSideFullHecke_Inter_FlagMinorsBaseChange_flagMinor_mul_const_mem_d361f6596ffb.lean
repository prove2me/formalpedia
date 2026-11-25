-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMinorsBaseChange_flagMinor_mul_const_mem_d361f6596ffb
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMinorsBaseChange_flagMinor_mul_const_mem_d361f6596ffb
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:21:17.176403+00:00
-- url     : https://prove2.me/theorems/e646aa98-f5e8-55d4-b325-04f910355374
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Minors Base Change flag Minor mul const mem d361f6596ffb: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hec
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Minors Base Change flag Minor mul const mem d361f6596ffb construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Minors Base Change flag Minor mul const mem d361f6596ffb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMinorsBaseChange.lean#L14-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMinorsBaseChange.lean#L14-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMinorsBaseChange
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMinorsBaseChange

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMinorsBaseChange_flagMinor_mul_const_mem_d361f6596ffb {F : Type} [Field F] {σ : Type} {n m p : ℕ}
    (M : Matrix (Fin n) (Fin m) (MvPolynomial σ F)) (D : Matrix (Fin m) (Fin p) F)
    (N : Matrix (Fin n) (Fin p) (MvPolynomial σ F)) (hN : ∀ a b, N a b = ∑ k, M a k * C (D k b))
    (j : Fin (n - 1)) (S : PluckerBlocks p n j) :
    flagMinor N j S ∈
      Algebra.adjoin F (Set.range fun q : Σ j, PluckerBlocks m n j => flagMinor M q.1 q.2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«FlagMinorsBaseChange».«flagMinor_mul_const_mem» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMinorsBaseChange_flagMinor_mul_const_mem_d361f6596ffb
