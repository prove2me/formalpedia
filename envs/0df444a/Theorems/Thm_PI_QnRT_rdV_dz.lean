-- Prove2me | Theorems.Thm_PI_QnRT_rdV_dz
-- name    : PI.QnRT.rdV_dz
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:20:06.454659+00:00
-- url     : https://prove2.me/theorems/2f47ee24-50cf-4ac6-9128-55829a4ad9ab
-- title:
--   Qn RT: rd V dz
-- statement:
--   The Qn RT construction uses the rd V dz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/SecondHermitianPartDiagonal.lean#L265-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/SecondHermitianPartDiagonal.lean#L265-L293

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_WColOther
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_SecondHermitianPartDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.QnRT
variable {k r : ℕ}

theorem PI.QnRT.rdV_dz {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r) (D : Set (Mx k r))
    (f : Mx k r → E) (hf : SmoothLev k r l.castSucc D f) (c : Fin r → ℂ) (hc : c l ≠ 0)
    (g₁ : Mx k r) (hg₁ : g₁ ∈ Glev k r l.succ) (hD : w1 k r l (c l) * g₁ ∈ D) (κ : ℂ) :
    RdV (dz l κ (-star κ)) f (w1 k r l (c l) * g₁) =
      fderiv ℝ (fun c' : Fin r → ℂ => f (w1 k r l (c' l) * g₁)) c (Pi.single l (c l * κ)) := by sorry
