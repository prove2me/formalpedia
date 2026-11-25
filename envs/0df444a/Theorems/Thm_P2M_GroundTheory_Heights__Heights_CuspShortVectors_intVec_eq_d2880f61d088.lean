-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CuspShortVectors_intVec_eq_d2880f61d088
-- name    : P2M_GroundTheory_Heights__Heights_CuspShortVectors_intVec_eq_d2880f61d088
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:13.517542+00:00
-- url     : https://prove2.me/theorems/86d34851-913a-4fff-b106-f445af5524bf
-- title:
--   P2 M Ground Theory Heights  Heights Cusp Short Vectors int Vec eq d2880f61d088: P2 M Ground Theory Heights  Heights Cusp Short Vectors int Vec eq d2880f61d088
-- statement:
--   The P2 M Ground Theory Heights  Heights Cusp Short Vectors int Vec eq d2880f61d088 construction uses the P2 M Ground Theory Heights  Heights Cusp Short Vectors int Vec eq d2880f61d088 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspShortVectors.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspShortVectors.lean#L15-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspShortVectors
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
open GroundTheory.Heights₂.Heights.CuspShortVectors

theorem P2M_GroundTheory_Heights__Heights_CuspShortVectors_intVec_eq_d2880f61d088 {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a n : Fin g → ℤ) :
    intVecC a + τ *ᵥ intVecC n =
      (fun k => ((a k : ℝ) : ℂ)) + τ *ᵥ fun k => ((n k : ℝ) : ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CuspShortVectors».«intVec_eq» := P2M_GroundTheory_Heights__Heights_CuspShortVectors_intVec_eq_d2880f61d088
