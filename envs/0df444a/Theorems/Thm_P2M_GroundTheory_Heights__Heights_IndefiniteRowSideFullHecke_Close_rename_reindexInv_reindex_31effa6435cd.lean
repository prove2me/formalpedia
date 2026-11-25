-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_rename_reindexInv_reindex_31effa6435cd
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_rename_reindexInv_reindex_31effa6435cd
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:16:28.94853+00:00
-- url     : https://prove2.me/theorems/79fbb043-ab40-52c8-91f2-e239c5b4e1dc
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close rename reindex Inv reindex 31effa6435cd: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close rename reinde
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close rename reindex Inv reindex 31effa6435cd construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close rename reindex Inv reindex 31effa6435cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L121-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L121-L127

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_rename_reindexInv_reindex_31effa6435cd (f : MvPolynomial (Coord (oneBlockSizes e r)) ℤ) :
    rename (oneBlockReindexInv e r) (rename (oneBlockReindex e r) f) = f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«rename_reindexInv_reindex» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_rename_reindexInv_reindex_31effa6435cd
