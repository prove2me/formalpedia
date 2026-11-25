-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_BoundedMonomials_equiv_f77c21673c51
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_BoundedMonomials_equiv_f77c21673c51
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:15:53.135283+00:00
-- url     : https://prove2.me/theorems/70fcd08f-3283-524a-b6ff-4046882af625
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Bounded Monomials equiv f77c21673c51: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Bounded Monomial
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Bounded Monomials equiv f77c21673c51 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Bounded Monomials equiv f77c21673c51 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ChartFormEvalAgree.lean#L42-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ChartFormEvalAgree.lean#L42-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ChartFormEvalAgree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_BoundedMonomials_equiv_f77c21673c51 :
    GroundTheory.Heights₂.Heights.BoundedMonomials.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.BoundedMonomials.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«BoundedMonomials».«equiv» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_BoundedMonomials_equiv_f77c21673c51
