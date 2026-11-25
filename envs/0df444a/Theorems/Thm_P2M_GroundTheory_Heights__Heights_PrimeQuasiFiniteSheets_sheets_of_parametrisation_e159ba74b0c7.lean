-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_sheets_of_parametrisation_e159ba74b0c7
-- name    : P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_sheets_of_parametrisation_e159ba74b0c7
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:16:02.039875+00:00
-- url     : https://prove2.me/theorems/dfdf7506-17c6-4771-be4f-a7403d0ee8fd
-- title:
--   P2 M Ground Theory Heights  Heights Prime Quasi Finite Sheets sheets of parametrisation e159ba74b0c7: P2 M Ground Theory Heights  Heights Prime Quasi Finite Sheets sheets of parametrisation e159ba74b0
-- statement:
--   The P2 M Ground Theory Heights  Heights Prime Quasi Finite Sheets sheets of parametrisation e159ba74b0c7 construction uses the P2 M Ground Theory Heights  Heights Prime Quasi Finite Sheets sheets of parametrisation e159ba74b0c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPrimeQuasiFiniteSheets.lean#L67-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPrimeQuasiFiniteSheets.lean#L67-L176

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimeQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFiniteFibresDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StDominantPrimitiveFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSimpleRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPrimeQuasiFiniteSheets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.PrimeQuasiFiniteSheets
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_sheets_of_parametrisation_e159ba74b0c7 (hSR : ComplexSets.SimpleRootBranch.Statement)
    {Q : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (c : Fin n → ℂ) (m : Polynomial (MvPolynomial (Fin d) ℂ)) (Δ : MvPolynomial (Fin d) ℂ)
    (S : Fin n → Polynomial (MvPolynomial (Fin d) ℂ))
    (hP : ∀ y : Fin d → ℂ, eval y Δ ≠ 0 →
      (m.map (eval y)).natDegree = m.natDegree ∧ (m.map (eval y)).Separable ∧
      (∀ x ∈ ComplexSets.fibre Q A y, (m.map (eval y)).IsRoot (∑ j, c j * x j) ∧
        ∀ j, eval y Δ * x j = ((S j).map (eval y)).eval (∑ k, c k * x k)) ∧
      ∀ τ : ℂ, (m.map (eval y)).IsRoot τ → ∃ x ∈ ComplexSets.fibre Q A y, ∑ j, c j * x j = τ)
    (y : Fin d → ℂ) (hy : eval y Δ ≠ 0) :
    ∃ (U : Set (Fin d → ℂ)) (N : ℕ) (s : Fin N → (Fin d → ℂ) → Fin n → ℂ),
      IsOpen U ∧ y ∈ U ∧ (∀ j, DifferentiableOn ℂ (s j) U) ∧
      ∀ y' ∈ U, (∀ j, s j y' ∈ ComplexSets.fibre Q A y') ∧
        Function.Injective (fun j => s j y') ∧
        ComplexSets.fibre Q A y' ⊆ Set.range (fun j => s j y') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PrimeQuasiFiniteSheets».«sheets_of_parametrisation» := P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_sheets_of_parametrisation_e159ba74b0c7
