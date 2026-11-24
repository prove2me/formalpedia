-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_herm_iso
-- name    : PI.PolynomialProperness.CoreW.herm_iso
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:15:35.639342+00:00
-- url     : https://prove2.me/theorems/07bfbcec-1570-425a-af04-37c1d23e8a5a
-- title:
--   Core W: herm iso
-- statement:
--   The Core W construction uses the herm iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L78-L81

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
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
open PI PI.PolynomialProperness PI.PolynomialProperness.CoreW
variable {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)

theorem PI.PolynomialProperness.CoreW.herm_iso (s : Matrix (Fin n) (Fin n) ℂ) (hs : sᴴ * H * s = H) (v w : Fin n → ℂ) :
    herm H (s *ᵥ v) (s *ᵥ w) = herm H v w := by sorry
