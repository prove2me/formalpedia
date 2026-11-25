-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_aff
-- name    : PI.TwistedEisensteinNonvanishing.W.qt_aff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:08.93962+00:00
-- url     : https://prove2.me/theorems/250953be-8199-4556-9066-b54e1482d620
-- title:
--   W: qt aff
-- statement:
--   The W construction uses the qt aff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/ChangeVariablesDeterminantOne.lean#L104-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/ChangeVariablesDeterminantOne.lean#L104-L113

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

theorem PI.TwistedEisensteinNonvanishing.W.qt_aff (L : (ι → E) ≃ₗ[E] (ι → E)) (τ : ι → E) :
    QT P (fun t => L t + τ) ((qOf P : K) ^ vq P (LinearMap.det (L : (ι → E) →ₗ[E] (ι → E)))) := by sorry
