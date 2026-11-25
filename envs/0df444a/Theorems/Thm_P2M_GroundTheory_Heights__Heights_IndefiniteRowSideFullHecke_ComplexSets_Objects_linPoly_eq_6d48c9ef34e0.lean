-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_Objects_linPoly_eq_6d48c9ef34e0
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_Objects_linPoly_eq_6d48c9ef34e0
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:20:22.794555+00:00
-- url     : https://prove2.me/theorems/f8964e8b-65ac-4f4f-bac5-cc7cd142964c
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Objects lin Poly eq 6d48c9ef34e0: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Object
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Objects lin Poly eq 6d48c9ef34e0 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Objects lin Poly eq 6d48c9ef34e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/ProjDegreeEqFinrankAdjoin.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/ProjDegreeEqFinrankAdjoin.lean#L16-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_IsClosedComplexSubmanifoldIn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ProjDegreeEqFinrankAdjoin
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
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.Objects
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_Objects_linPoly_eq_6d48c9ef34e0 (A : Matrix (Fin d) (Fin n) ℂ) (i : Fin d) :
    linPoly A.mulVecLin i = GroundTheory.Heights₂.Heights.ComplexSets.linPoly A i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«Objects».«linPoly_eq» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_Objects_linPoly_eq_6d48c9ef34e0
