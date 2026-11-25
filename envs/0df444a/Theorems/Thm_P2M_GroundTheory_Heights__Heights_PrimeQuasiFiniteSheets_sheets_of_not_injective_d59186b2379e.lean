-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_sheets_of_not_injective_d59186b2379e
-- name    : P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_sheets_of_not_injective_d59186b2379e
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:15:44.411166+00:00
-- url     : https://prove2.me/theorems/587286dc-e0c8-4780-8e33-57f0bbc3da99
-- title:
--   P2 M Ground Theory Heights  Heights Prime Quasi Finite Sheets sheets of not injective d59186b2379e: P2 M Ground Theory Heights  Heights Prime Quasi Finite Sheets sheets of not injective d59186b2379e
-- statement:
--   The P2 M Ground Theory Heights  Heights Prime Quasi Finite Sheets sheets of not injective d59186b2379e construction uses the P2 M Ground Theory Heights  Heights Prime Quasi Finite Sheets sheets of not injective d59186b2379e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPrimeQuasiFiniteSheets.lean#L28-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPrimeQuasiFiniteSheets.lean#L28-L50

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

theorem P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_sheets_of_not_injective_d59186b2379e (Q : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hinj : ¬ Function.Injective (ComplexSets.projHom Q A)) :
    ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧ ∀ y : Fin d → ℂ, eval y c ≠ 0 →
      ∃ (U : Set (Fin d → ℂ)) (N : ℕ) (s : Fin N → (Fin d → ℂ) → Fin n → ℂ),
        IsOpen U ∧ y ∈ U ∧ (∀ j, DifferentiableOn ℂ (s j) U) ∧
        ∀ y' ∈ U, (∀ j, s j y' ∈ ComplexSets.fibre Q A y') ∧
          Function.Injective (fun j => s j y') ∧
          ComplexSets.fibre Q A y' ⊆ Set.range (fun j => s j y') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PrimeQuasiFiniteSheets».«sheets_of_not_injective» := P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_sheets_of_not_injective_d59186b2379e
