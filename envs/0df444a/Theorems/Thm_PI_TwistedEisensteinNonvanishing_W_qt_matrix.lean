-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_matrix
-- name    : PI.TwistedEisensteinNonvanishing.W.qt_matrix
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:30:20.500404+00:00
-- url     : https://prove2.me/theorems/e014f787-1e04-41ee-95c5-9d4dc59dfd11
-- title:
--   W: qt matrix
-- statement:
--   The W construction uses the qt matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/ChangeVariablesDeterminantOne.lean#L58-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/ChangeVariablesDeterminantOne.lean#L58-L85

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumToGaussSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_ChangeVariablesDeterminantOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE Function Matrix
variable {E K : Type} [Field E] [NumberField E] [Field K]
variable {P : HeightOneSpectrum (𝓞 E)} (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hK : ((qOf P : ℕ) : K) ≠ 0)
include hN hp hq hK
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem PI.TwistedEisensteinNonvanishing.W.qt_matrix (M : Matrix ι ι E) (hM : M.det ≠ 0) :
    QT P (fun v => M *ᵥ v) ((qOf P : K) ^ vq P M.det) := by sorry
