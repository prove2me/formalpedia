-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CuspLeadingMinima_single_mem_leadingLattice_83159460311d
-- name    : P2M_GroundTheory_Heights__Heights_CuspLeadingMinima_single_mem_leadingLattice_83159460311d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:18.390107+00:00
-- url     : https://prove2.me/theorems/9320ad9c-e913-567e-839c-a2297097f613
-- title:
--   P2 M Ground Theory Heights  Heights Cusp Leading Minima single mem leading Lattice 83159460311d: P2 M Ground Theory Heights  Heights Cusp Leading Minima single mem leading Lattice 83159460311d
-- statement:
--   The P2 M Ground Theory Heights  Heights Cusp Leading Minima single mem leading Lattice 83159460311d construction uses the P2 M Ground Theory Heights  Heights Cusp Leading Minima single mem leading Lattice 83159460311d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspLeadingMinima.lean#L15-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspLeadingMinima.lean#L15-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspLeadingMinima
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.CuspLeadingMinima

theorem P2M_GroundTheory_Heights__Heights_CuspLeadingMinima_single_mem_leadingLattice_83159460311d {g r : ℕ} (h : r ≤ g) (j : Fin r) :
    Pi.single (Fin.castLE h j) (1 : ℂ) ∈ leadingLattice g r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CuspLeadingMinima».«single_mem_leadingLattice» := P2M_GroundTheory_Heights__Heights_CuspLeadingMinima_single_mem_leadingLattice_83159460311d
