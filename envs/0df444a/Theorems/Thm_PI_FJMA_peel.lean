-- Prove2me | Theorems.Thm_PI_FJMA_peel
-- name    : PI.FJMA.peel
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:37.204865+00:00
-- url     : https://prove2.me/theorems/c81f658e-c345-55cc-b8f9-1c0e966c9412
-- title:
--   FJMA: peel
-- statement:
--   The FJMA construction uses the peel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/VarsZeroOfSupported.lean#L86-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/VarsZeroOfSupported.lean#L86-L114

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_VarsZeroOfSupported
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMA
open PI.FJM
variable {σ : Type}

theorem PI.FJMA.peel (hC : CauchyHW) {m n : ℕ} (ι : Fin m × Fin n → σ) (hι : Function.Injective ι)
    (α : Fin m → ℕ) (β : Fin n → ℕ) (S : Set σ) (F G : MvPolynomial σ ℂ) (hF : F ∈ supported ℂ S)
    (hF0 : F ≠ 0) (hG : FreeOf S G) (hS : ∀ x, ι x ∉ S) (hG0 : G ≠ 0) (hP : IsBlockHighestWeight ι α β (F * G)) :
    SqFacts α β ∧ ∃ Q, FreeOf (Set.range ι) Q ∧
      G = shapeProd (Matrix.of fun i k => (X (ι (i, k)) : MvPolynomial σ ℂ)) (List.ofFn α) * Q := by sorry
