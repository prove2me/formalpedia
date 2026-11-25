-- Prove2me | Theorems.Thm_P2M_PI_PolynomialProperness_CB_isUnit_det_monomialMatrix__59e50fe8fbb4
-- name    : P2M_PI_PolynomialProperness_CB_isUnit_det_monomialMatrix__59e50fe8fbb4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:57:44.246788+00:00
-- url     : https://prove2.me/theorems/fdc84143-8f4f-439b-a0bd-7ad4a9d8d505
-- title:
--   P2 M PI Polynomial Properness CB is Unit det monomial Matrix  59e50fe8fbb4: P2 M PI Polynomial Properness CB is Unit det monomial Matrix  59e50fe8fbb4
-- statement:
--   The P2 M PI Polynomial Properness CB is Unit det monomial Matrix  59e50fe8fbb4 construction uses the P2 M PI Polynomial Properness CB is Unit det monomial Matrix  59e50fe8fbb4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/SecondOrderNormBound.lean#L121-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/SecondOrderNormBound.lean#L121-L133

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_SecondOrderNormBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.CB

theorem P2M_PI_PolynomialProperness_CB_isUnit_det_monomialMatrix__59e50fe8fbb4 {m : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) :
    IsUnit (monoP w d).det := by sorry

alias «PI».«PolynomialProperness».«CB».«isUnit_det_monomialMatrix'» := P2M_PI_PolynomialProperness_CB_isUnit_det_monomialMatrix__59e50fe8fbb4
