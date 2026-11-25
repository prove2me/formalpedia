-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_stdLatticeExt_iff_15805c108319
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_stdLatticeExt_iff_15805c108319
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:20:12.885296+00:00
-- url     : https://prove2.me/theorems/f5937cd4-7686-46e0-8227-ea0b5f5832c5
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem std Lattice Ext iff 15805c108319: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem std Lattice
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem std Lattice Ext iff 15805c108319 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem std Lattice Ext iff 15805c108319 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L260-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L260-L300

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses
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
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (mConeMap mCoordIdeal mcPts)
noncomputable section
variable {K : Type} [Field K] [NumberField K] {K' : Type} [Field K'] [NumberField K'] [Algebra K K']
  {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_stdLatticeExt_iff_15805c108319 (x : Fin n → K') :
    x ∈ stdLatticeExt K K' n ↔ ∀ j, IsIntegral ℤ (x j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«mem_stdLatticeExt_iff» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_stdLatticeExt_iff_15805c108319
