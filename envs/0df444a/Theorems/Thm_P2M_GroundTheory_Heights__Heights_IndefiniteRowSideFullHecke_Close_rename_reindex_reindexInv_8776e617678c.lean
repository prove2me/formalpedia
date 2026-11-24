-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_rename_reindex_reindexInv_8776e617678c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_rename_reindex_reindexInv_8776e617678c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:25:39.345823+00:00
-- url     : https://prove2.me/theorems/f0f99ddf-dd0f-46d4-a8d9-0ca899286785
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close rename reindex reindex Inv 8776e617678c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close rename reinde
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close rename reindex reindex Inv 8776e617678c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close rename reindex reindex Inv 8776e617678c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L113-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L113-L119

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_rename_reindex_reindexInv_8776e617678c (g : MvPolynomial (Σ _ : Unit, Fin (e + 1) × Fin (r + 1)) ℤ) :
    rename (oneBlockReindex e r) (rename (oneBlockReindexInv e r) g) = g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«rename_reindex_reindexInv» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_rename_reindex_reindexInv_8776e617678c
