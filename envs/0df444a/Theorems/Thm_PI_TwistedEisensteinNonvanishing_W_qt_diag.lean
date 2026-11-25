-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_diag
-- name    : PI.TwistedEisensteinNonvanishing.W.qt_diag
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:30:31.993813+00:00
-- url     : https://prove2.me/theorems/a3097e10-9317-402b-afc1-8f9a195200dd
-- title:
--   W: qt diag
-- statement:
--   The W construction uses the qt diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/ChangeVariablesDeterminantOne.lean#L38-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/ChangeVariablesDeterminantOne.lean#L38-L56

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

theorem PI.TwistedEisensteinNonvanishing.W.qt_diag (D : ι → E) (hD : ∀ i, D i ≠ 0) :
    QT P (fun v => diagonal D *ᵥ v) ((qOf P : K) ^ vq P (diagonal D).det) := by sorry
