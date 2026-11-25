-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_gelfand_psM
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.gelfand_psM
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:03:58.525073+00:00
-- url     : https://prove2.me/theorems/8e5507a1-a01e-4d8b-8096-10ac5cad2328
-- title:
--   S7: gelfand ps M
-- statement:
--   The S7 construction uses the gelfand ps M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPs.lean#L58-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPs.lean#L58-L89

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhi
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.gelfand_psM (T : KType ε Λ) (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) :
    ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ posSet n ⊆ U ∧ DifferentiableOn ℂ (psM T μ) U ∧
      ∀ z ∈ U, ∀ k : ℕ,
        opGelfand (fun a b => Lhol (Matrix.single a b (1 : ℂ))) k (psM T μ) z =
            ((-1 : ℂ) ^ k * gval (icShift lam) k) • psM T μ z ∧
          opGelfand (fun a b => Lhol (Matrix.single (Fin.rev b) (Fin.rev a) (1 : ℂ))) k (psM T μ) z =
            gval (icShift (-lam)) k • psM T μ z := by sorry
