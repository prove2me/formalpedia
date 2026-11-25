-- Prove2me | Theorems.Thm_PI_PolynomialProperness_frame_mulVec_fmul
-- name    : PI.PolynomialProperness.frame_mulVec_fmul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:19:13.845714+00:00
-- url     : https://prove2.me/theorems/85bd03eb-870a-5c7b-99d3-ae2313e59ca7
-- title:
--   Polynomial Properness: frame mul Vec fmul
-- statement:
--   The Polynomial Properness construction uses the frame mul Vec fmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/AddLeMulPowOfSqLeOfLeMul.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/AddLeMulPowOfSqLeOfLeMul.lean#L14-L24

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_AddLeMulPowOfSqLeOfLeMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness

theorem PI.PolynomialProperness.frame_mulVec_fmul {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {σ : B.Mat k r}
    {v : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (h : ∀ b, σ *ᵥ fvec k r z b = fmul k r z v b)
    (c : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (b : Fin (r + 1)) :
    σ *ᵥ fmul k r z c b = fmul k r z (v * c) b := by sorry
