-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CuspShortVectors_value_ge_7bf05fb7e899
-- name    : P2M_GroundTheory_Heights__Heights_CuspShortVectors_value_ge_7bf05fb7e899
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:49.633847+00:00
-- url     : https://prove2.me/theorems/332d93bc-7945-444e-9317-60d81cc6bbde
-- title:
--   P2 M Ground Theory Heights  Heights Cusp Short Vectors value ge 7bf05fb7e899: P2 M Ground Theory Heights  Heights Cusp Short Vectors value ge 7bf05fb7e899
-- statement:
--   The P2 M Ground Theory Heights  Heights Cusp Short Vectors value ge 7bf05fb7e899 construction uses the P2 M Ground Theory Heights  Heights Cusp Short Vectors value ge 7bf05fb7e899 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspShortVectors.lean#L26-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspShortVectors.lean#L26-L66

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

theorem P2M_GroundTheory_Heights__Heights_CuspShortVectors_value_ge_7bf05fb7e899 {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (hY : (τ.map Complex.im).PosDef)
    {c M : ℝ} (hM : 0 < M)
    (hcY : ∀ x : Fin g → ℝ, c * ∑ k, x k ^ 2 ≤ MCSchur.qf (τ.map Complex.im) x)
    (hPH : PeriodHermValue.Statement) (r : ℕ)
    (hdiag : ∀ k : Fin g, r ≤ k.val → (τ.map Complex.im) k k ≤ M) (a n : Fin g → ℤ)
    (h : n ≠ 0 ∨ ∃ k : Fin g, r ≤ k.val ∧ a k ≠ 0) :
    min c (1 / M) ≤ hermValue (τ.map Complex.im)⁻¹ (intVecC a + τ *ᵥ intVecC n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CuspShortVectors».«value_ge» := P2M_GroundTheory_Heights__Heights_CuspShortVectors_value_ge_7bf05fb7e899
