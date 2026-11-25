-- Prove2me | Theorems.Thm_P2M_PI_FockOneDegW_Core_exists_monomial_weight__7e76f9f36b77
-- name    : P2M_PI_FockOneDegW_Core_exists_monomial_weight__7e76f9f36b77
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:57:38.087903+00:00
-- url     : https://prove2.me/theorems/70bc9fdb-b727-40a6-822d-1998dc7189e3
-- title:
--   P2 M PI Fock One Deg W Core exists monomial weight  7e76f9f36b77: P2 M PI Fock One Deg W Core exists monomial weight  7e76f9f36b77
-- statement:
--   The P2 M PI Fock One Deg W Core exists monomial weight  7e76f9f36b77 construction uses the P2 M PI Fock One Deg W Core exists monomial weight  7e76f9f36b77 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/ExistsMonomialWeight.lean#L255-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/ExistsMonomialWeight.lean#L255-L273

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
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
open PI PI.FockOneDegW PI.FockOneDegW.Core
open PI.FockOneDegW PI.FockOneDegW.Inner PI.FockOneDegW.Diag
variable {p q r s : ℕ}

theorem P2M_PI_FockOneDegW_Core_exists_monomial_weight__7e76f9f36b77 {σ ι : Type*} [Fintype σ]
    (T : ι → Module.End ℂ (MvPolynomial σ ℂ)) (f : ι → (σ →₀ ℕ) → ℚ)
    (hT : ∀ a β, T a (MvPolynomial.monomial β 1) =
      ((f a β : ℚ) : ℂ) • MvPolynomial.monomial β 1)
    (μ : ι → ℚ) (d : ℕ) (P : MvPolynomial σ ℂ) (hP : P ∈ homog σ d) (h0 : P ≠ 0)
    (hw : ∀ a, (T a - ((μ a : ℚ) : ℂ) • (LinearMap.id : Module.End ℂ (MvPolynomial σ ℂ))) P = 0) :
    ∃ α : σ →₀ ℕ, MvPolynomial.coeff α P ≠ 0 ∧ ∑ i, α i = d ∧ ∀ a, μ a = f a α := by sorry

alias «PI».«FockOneDegW».«Core».«exists_monomial_weight'» := P2M_PI_FockOneDegW_Core_exists_monomial_weight__7e76f9f36b77
