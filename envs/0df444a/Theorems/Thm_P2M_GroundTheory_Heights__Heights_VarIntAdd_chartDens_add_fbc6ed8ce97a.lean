-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarIntAdd_chartDens_add_fbc6ed8ce97a
-- name    : P2M_GroundTheory_Heights__Heights_VarIntAdd_chartDens_add_fbc6ed8ce97a
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:46:28.599017+00:00
-- url     : https://prove2.me/theorems/829dbe74-be26-5225-9d9d-560e1ec638dd
-- title:
--   P2 M Ground Theory Heights  Heights Var Int Add chart Dens add fbc6ed8ce97a: P2 M Ground Theory Heights  Heights Var Int Add chart Dens add fbc6ed8ce97a
-- statement:
--   The P2 M Ground Theory Heights  Heights Var Int Add chart Dens add fbc6ed8ce97a construction uses the P2 M Ground Theory Heights  Heights Var Int Add chart Dens add fbc6ed8ce97a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarIntAdd.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarIntAdd.lean#L47-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarIntAdd
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
open MvPolynomial MeasureTheory ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.VarIntAdd

theorem P2M_GroundTheory_Heights__Heights_VarIntAdd_chartDens_add_fbc6ed8ce97a {n k : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin k) (Fin n) ℂ}
    (hfin : ∀ y, (fibre J A y).Finite) (f g : (Fin n → ℂ) → ℝ) (φ : Fin k → (Fin n → ℂ) → ℝ) :
    chartDens J A (f + g) φ = chartDens J A f φ + chartDens J A g φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VarIntAdd».«chartDens_add» := P2M_GroundTheory_Heights__Heights_VarIntAdd_chartDens_add_fbc6ed8ce97a
