-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_gram_image
-- name    : PI.PolynomialProperness.CoreW.gram_image
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:30:45.942907+00:00
-- url     : https://prove2.me/theorems/af43b360-29d7-4246-a4f5-d426a7d8d164
-- title:
--   Core W: gram image
-- statement:
--   The Core W construction uses the gram image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/IsoRightInv.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/IsoRightInv.lean#L48-L52

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

theorem PI.PolynomialProperness.CoreW.gram_image (H s : Matrix (Fin n) (Fin n) ℂ) (hs : sᴴ * H * s = H) (m : ι → Fin n → ℂ) :
    gramOf H (fun i => s *ᵥ m i) = gramOf H m := by sorry
