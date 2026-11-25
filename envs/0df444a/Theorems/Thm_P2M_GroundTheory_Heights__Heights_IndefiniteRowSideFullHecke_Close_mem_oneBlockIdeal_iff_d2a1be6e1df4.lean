-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_oneBlockIdeal_iff_d2a1be6e1df4
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_oneBlockIdeal_iff_d2a1be6e1df4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:35.921963+00:00
-- url     : https://prove2.me/theorems/14f30d34-df64-4087-aef2-b75b64c8802f
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem one Block Ideal iff d2a1be6e1df4: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem one Block Id
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem one Block Ideal iff d2a1be6e1df4 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem one Block Ideal iff d2a1be6e1df4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L147-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L147-L153

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
variable {K : Type} [Field K] [NumberField K] {e r : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_oneBlockIdeal_iff_d2a1be6e1df4 (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K))
    (f : MvPolynomial (Coord (oneBlockSizes e r)) ℤ) :
    f ∈ Heights.oneBlockIdeal (r := r) om ↔
      rename (oneBlockReindex e r) f ∈ mCoordIdeal (oneBlockPt om r) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«mem_oneBlockIdeal_iff» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_oneBlockIdeal_iff_d2a1be6e1df4
