-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_psd_image
-- name    : PI.PolynomialProperness.CoreW.psd_image
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:30:56.190612+00:00
-- url     : https://prove2.me/theorems/639dcf47-c920-43a0-984a-9151ad3a043d
-- title:
--   Core W: psd image
-- statement:
--   The Core W construction uses the psd image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/IsoRightInv.lean#L37-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/IsoRightInv.lean#L37-L46

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

theorem PI.PolynomialProperness.CoreW.psd_image (H s : Matrix (Fin n) (Fin n) ℂ) (hHH : H * H = 1) (hs : sᴴ * H * s = H)
    (m : ι → Fin n → ℂ) (hpsd : ∀ x, (∀ i, herm H x (m i) = 0) → 0 ≤ (herm H x x).re)
    (w : Fin n → ℂ) (hw : ∀ i, herm H w (s *ᵥ m i) = 0) : 0 ≤ (herm H w w).re := by sorry
