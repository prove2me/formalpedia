-- Prove2me | Theorems.Thm_PI_FinOrdValD_WA_exists_near
-- name    : PI.FinOrdValD.WA.exists_near
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:30:41.006631+00:00
-- url     : https://prove2.me/theorems/28115afd-8aa0-4a94-8a05-a5d8a37d85fd
-- title:
--   WA: exists near
-- statement:
--   The WA construction uses the exists near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderValuation/WeakApprox.lean#L69-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderValuation/WeakApprox.lean#L69-L87

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderValuation_WeakApprox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open PI PI.FinOrdValD PI.FinOrdValD.WA
variable {L : Type*} [Field L] [NumberField L]

theorem PI.FinOrdValD.WA.exists_near (v : HeightOneSpectrum (𝓞 L)) (x : v.adicCompletion L) {δ : ℤᵐ⁰} (hδ : δ ≠ 0) :
    ∃ b : L, Valued.v (algebraMap L (v.adicCompletion L) b - x) < δ := by sorry
