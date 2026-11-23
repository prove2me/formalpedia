-- Prove2me | Theorems.Thm_PI_FinOrdValD_WA_exists_nat_small
-- name    : PI.FinOrdValD.WA.exists_nat_small
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:55.420844+00:00
-- url     : https://prove2.me/theorems/ba6f43d3-a7aa-492c-ae9a-006bbbd5588e
-- title:
--   WA: exists nat small
-- statement:
--   The WA construction uses the exists nat small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderValuation/WeakApprox.lean#L40-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderValuation/WeakApprox.lean#L40-L67

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

theorem PI.FinOrdValD.WA.exists_nat_small (T : Finset (HeightOneSpectrum (𝓞 L))) (δ : HeightOneSpectrum (𝓞 L) → ℤᵐ⁰)
    (hδ : ∀ v ∈ T, δ v ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ v ∈ T, v.valuation L (N : L) < δ v := by sorry
