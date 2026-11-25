-- Prove2me | Theorems.Thm_PI_Dv_ProjAW_span_cut_eq
-- name    : PI.Dv.ProjAW.span_cut_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:28:54.539234+00:00
-- url     : https://prove2.me/theorems/86f18ca3-5cb4-48f1-a59c-2331b5a0cee9
-- title:
--   Proj AW: span cut eq
-- statement:
--   The Proj AW construction uses the span cut eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/LenAtEqZero.lean#L59-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/LenAtEqZero.lean#L59-L73

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_LenAtEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (A : HLat K)

theorem PI.Dv.ProjAW.span_cut_eq {f : Module.End K A.V} (hf : f * f = f) {n : ℕ} (hn0 : 0 < n)
    (hn : ∀ x ∈ A.L, ((n : ℕ) : 𝓞 K) • f x ∈ A.L) :
    Submodule.span K (imgE A f A.L : Set A.V) = Submodule.span K (cutE A f A.L : Set A.V) := by sorry
