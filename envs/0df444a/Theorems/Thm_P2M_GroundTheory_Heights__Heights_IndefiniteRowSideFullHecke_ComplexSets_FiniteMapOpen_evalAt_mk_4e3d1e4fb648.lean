-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_evalAt_mk_4e3d1e4fb648
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_evalAt_mk_4e3d1e4fb648
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:15.852009+00:00
-- url     : https://prove2.me/theorems/1e92a3d1-e615-4eb6-a6be-976803beae9e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Finite Map Open eval At mk 4e3d1e4fb648: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Finite Map Open eval At mk 4e3d1e4fb648 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Finite Map Open eval At mk 4e3d1e4fb648 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteMapOpen.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteMapOpen.lean#L75-L77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
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
open MvPolynomial Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_evalAt_mk_4e3d1e4fb648 (J : Ideal (MvPolynomial (Fin n) ℂ)) {z : Fin n → ℂ} (hz : z ∈ zeroLocus J)
    (q : MvPolynomial (Fin n) ℂ) : evalAt J hz (Ideal.Quotient.mk J q) = eval z q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«FiniteMapOpen».«evalAt_mk» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_evalAt_mk_4e3d1e4fb648
