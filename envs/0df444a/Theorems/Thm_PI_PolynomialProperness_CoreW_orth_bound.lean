-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_orth_bound
-- name    : PI.PolynomialProperness.CoreW.orth_bound
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:38:42.424798+00:00
-- url     : https://prove2.me/theorems/584bd588-2524-4e35-a577-758caa1db27a
-- title:
--   Core W: orth bound
-- statement:
--   The Core W construction uses the orth bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/IsoRightInv.lean#L54-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/IsoRightInv.lean#L54-L112

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

theorem PI.PolynomialProperness.CoreW.orth_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (Γi : Matrix ι ι ℂ) (q : ι → Fin n → ℂ) (hG : gramOf H q * Γi = 1) (R : ℝ) (hR : 0 ≤ R)
    (hq : ∀ k, eN (q k) ≤ R) (hpsd : ∀ w, (∀ i, herm H w (q i) = 0) → 0 ≤ (herm H w w).re)
    (v : Fin n → ℂ) (hv : ∀ j, herm H v (q j) = 0) :
    nsq v ≤ (1 + (Fintype.card ι : ℝ) * (∑ j, ∑ k, ‖Γi j k‖) * (R * R)) * (herm H v v).re := by sorry
