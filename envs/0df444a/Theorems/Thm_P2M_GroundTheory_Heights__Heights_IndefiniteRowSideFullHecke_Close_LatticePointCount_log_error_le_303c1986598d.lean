-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LatticePointCount_log_error_le_303c1986598d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LatticePointCount_log_error_le_303c1986598d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:40.671371+00:00
-- url     : https://prove2.me/theorems/4258a0fe-dfbe-4f7d-93a6-ce2b5b971818
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Lattice Point Count log error le 303c1986598d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Lattice
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Lattice Point Count log error le 303c1986598d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Lattice Point Count log error le 303c1986598d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/HilbDegreeBoundAltOfStatement.lean#L8-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/HilbDegreeBoundAltOfStatement.lean#L8-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_HilbDegreeBoundAltOfStatement
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LatticePointCount_log_error_le_303c1986598d {C : ℝ} (hC : 0 ≤ C) (r : ℕ) :
    (r : ℝ) * Real.log (2 * (1 + r * C)) ≤
      (1 + Real.log (2 * (1 + C)) / Real.log 2) * (((r : ℝ) + 1) * Real.log ((r : ℝ) + 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«LatticePointCount».«log_error_le» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LatticePointCount_log_error_le_303c1986598d
