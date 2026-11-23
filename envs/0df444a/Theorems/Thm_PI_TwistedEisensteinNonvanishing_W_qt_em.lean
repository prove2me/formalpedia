-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_em
-- name    : PI.TwistedEisensteinNonvanishing.W.qt_em
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:26:43.795815+00:00
-- url     : https://prove2.me/theorems/a5ae365a-d588-4d33-9286-850f71d727d4
-- title:
--   W: qt em
-- statement:
--   The W construction uses the qt em property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/WeightedSumToGaussSum.lean#L58-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/WeightedSumToGaussSum.lean#L58-L185

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
variable {P : HeightOneSpectrum (𝓞 E)} (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hK : ((qOf P : ℕ) : K) ≠ 0)
include hN hp hq hK

theorem PI.TwistedEisensteinNonvanishing.W.qt_em {ι : Type} [Fintype ι] [DecidableEq ι] (k l : ι) {d : E} (hd : d ≠ 0) (c β : E)
    (hkl : l ≠ k ∨ c = 0) : QT P (em k l d c β) ((qOf P : K) ^ vq P d) := by sorry
