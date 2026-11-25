-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_iso_right_inv
-- name    : PI.PolynomialProperness.CoreW.iso_right_inv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:58:28.697969+00:00
-- url     : https://prove2.me/theorems/34d0e1d1-7291-4ab0-b292-8402ed023016
-- title:
--   Core W: iso right inv
-- statement:
--   The Core W construction uses the iso right inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/IsoRightInv.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/IsoRightInv.lean#L30-L35

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

theorem PI.PolynomialProperness.CoreW.iso_right_inv (H s : Matrix (Fin n) (Fin n) ℂ) (hHH : H * H = 1) (hs : sᴴ * H * s = H) :
    s * (H * sᴴ * H) = 1 := by sorry
