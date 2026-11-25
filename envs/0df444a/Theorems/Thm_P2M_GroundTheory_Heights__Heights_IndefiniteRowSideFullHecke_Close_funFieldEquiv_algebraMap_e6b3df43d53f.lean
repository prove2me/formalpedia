-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_algebraMap_e6b3df43d53f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_algebraMap_e6b3df43d53f
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:19:49.824795+00:00
-- url     : https://prove2.me/theorems/d4cc817c-a0c6-424b-a72b-01b4984e16fa
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close fun Field Equiv algebra Map e6b3df43d53f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close fun Field Eq
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close fun Field Equiv algebra Map e6b3df43d53f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close fun Field Equiv algebra Map e6b3df43d53f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/FunFieldEquivMemChartRingIff.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/FunFieldEquivMemChartRingIff.lean#L18-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_FunFieldEquivMemChartRingIff
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
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_algebraMap_e6b3df43d53f (P : ArithVariety n) (r : CoordRing P) :
    funFieldEquiv P (algebraMap (CoordRing P) P.FunField r) =
      algebraMap (CoordRing P) (FunField P) r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«funFieldEquiv_algebraMap» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_algebraMap_e6b3df43d53f
