-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_key_ineq
-- name    : PI.PolynomialProperness.CoreW.key_ineq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:14:24.475008+00:00
-- url     : https://prove2.me/theorems/56cfbf1c-6297-566a-a0f8-6628a1e7249f
-- title:
--   Core W: key ineq
-- statement:
--   The Core W construction uses the key ineq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/IsoRightInv.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/IsoRightInv.lean#L22-L28

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_IsoRightInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness
open PI.PolynomialProperness.CoreW
variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem PI.PolynomialProperness.CoreW.key_ineq (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (c : ℝ) (hc : 0 < c)
    (v y : Fin n → ℂ) (hvy : herm H v y = ((nsq v : ℝ) : ℂ)) (hyv : herm H y v = ((nsq v : ℝ) : ℂ))
    (hyy : (herm H y y).re ≤ c * nsq v) (hpos : 0 ≤ (herm H ((c : ℂ) • v - y) ((c : ℂ) • v - y)).re) :
    nsq v ≤ c * (herm H v v).re := by sorry
