-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_comp
-- name    : PI.TwistedEisensteinNonvanishing.W.qt_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:28:42.530092+00:00
-- url     : https://prove2.me/theorems/ba59b943-6e1f-4083-87ee-a699ded409d8
-- title:
--   W: qt comp
-- statement:
--   The W construction uses the qt comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/WeightedSumToGaussSum.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/WeightedSumToGaussSum.lean#L23-L31

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_SumSliceEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumToGaussSum
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
open Loc LocE Function
variable {E K : Type} [Field E] [NumberField E] [Field K]
variable (P : HeightOneSpectrum (𝓞 E)) {ι : Type} [Fintype ι] [DecidableEq ι]
variable {P}

theorem PI.TwistedEisensteinNonvanishing.W.qt_comp {T1 T2 : (ι → E) → (ι → E)} {c1 c2 : K} (h1 : QT P T1 c1) (h2 : QT P T2 c2) :
    QT P (fun t => T1 (T2 t)) (c2 * c1) := by sorry
