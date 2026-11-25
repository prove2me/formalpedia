-- Prove2me | Theorems.Thm_PI_KerDetFinW_comp_denom
-- name    : PI.KerDetFinW.comp_denom
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:33:14.223955+00:00
-- url     : https://prove2.me/theorems/afabec6e-a2a7-4ffc-a145-f969f2b8cc53
-- title:
--   Ker Det Fin W: comp denom
-- statement:
--   The Ker Det Fin W construction uses the comp denom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelFiniteness/ValuationLeOneOfDenom.lean#L66-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelFiniteness/ValuationLeOneOfDenom.lean#L66-L81

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ValuationLeOneOfDenom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KerDetFinW
open PI.KerIso

theorem PI.KerDetFinW.comp_denom {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E] {n : Type} [Fintype n]
    {M : Set E} {g g' : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)} {p : ℕ}
    (hg : AtP M g p) (hg' : AtP M g' p) (v : Fin 4 × n → K)
    (hv : ∀ w, v w ∈ (algebraMap (𝓞 K) K).range) :
    ∃ u : ℕ, Nat.Coprime u p ∧ ∀ w, (u : K) * (g.symm.trans g') v w ∈ (algebraMap (𝓞 K) K).range := by sorry
