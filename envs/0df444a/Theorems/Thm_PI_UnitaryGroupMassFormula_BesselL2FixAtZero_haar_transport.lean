-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_BesselL2FixAtZero_haar_transport
-- name    : PI.UnitaryGroupMassFormula.BesselL2FixAtZero.haar_transport
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:49:16.457299+00:00
-- url     : https://prove2.me/theorems/b81f6143-ffd0-4f83-b2fe-c35ebcb0ae65
-- title:
--   Bessel L2 Fix At Zero: haar transport
-- statement:
--   The Bessel L2 Fix At Zero construction uses the haar transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselSquareIntegrable/SchurHpk.lean#L47-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselSquareIntegrable/SchurHpk.lean#L47-L156

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselL2FixAtZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SchurHpkAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Closed
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SchurHpk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BesselL2FixAtZero
open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal
open PI.UpqRep PI.BesselL2FixAtZero
variable {n : ℕ} (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ)

theorem PI.UnitaryGroupMassFormula.BesselL2FixAtZero.haar_transport (hP : IsUnit P) (μ : Measure (Fin n → Fin n → ℂ)) [SigmaFinite μ] (h0 : μ ≠ 0)
    (hconc : μ {x | Matrix.of x ∉ PI.UpqRep.UH (Pᴴ * Jm ε * P)} = 0)
    (hinv : ∀ s ∈ PI.UpqRep.UH (Pᴴ * Jm ε * P), μ.map (fun x => Matrix.of.symm (s * Matrix.of x)) = μ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ = (c • muG ε).map (conjPrime₂ ε P) := by sorry
