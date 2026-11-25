-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_herm_expand
-- name    : PI.PolynomialProperness.CoreW.herm_expand
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:50.478803+00:00
-- url     : https://prove2.me/theorems/39bfd7c4-f487-5079-90db-e371bb15f5f7
-- title:
--   Core W: herm expand
-- statement:
--   The Core W construction uses the herm expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/IsoRightInv.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/IsoRightInv.lean#L14-L20

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

theorem PI.PolynomialProperness.CoreW.herm_expand (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (c : ℝ) (a b : Fin n → ℂ) :
    herm H ((c : ℂ) • a - b) ((c : ℂ) • a - b) =
      (c : ℂ) * ((c : ℂ) * herm H a a) - (c : ℂ) * herm H a b - ((c : ℂ) * herm H b a - herm H b b) := by sorry
