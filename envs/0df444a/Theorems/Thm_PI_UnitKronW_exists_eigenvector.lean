-- Prove2me | Theorems.Thm_PI_UnitKronW_exists_eigenvector
-- name    : PI.UnitKronW.exists_eigenvector
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:24.724355+00:00
-- url     : https://prove2.me/theorems/82cfc84d-f38b-4c53-88cd-08523a8936fe
-- title:
--   Unit Kron W: exists eigenvector
-- statement:
--   The Unit Kron W construction uses the exists eigenvector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitKronecker/PosDefFormNeZero.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitKronecker/PosDefFormNeZero.lean#L18-L20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_Development
import Definitions.Def_Lemmata_GeneralBFactRightBis_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_PosDefFormNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitKronW
open Matrix Polynomial ComplexOrder

theorem PI.UnitKronW.exists_eigenvector {k : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (μ : ℂ) (hμ : G.charpoly.IsRoot μ) :
    ∃ v : Fin k → ℂ, v ≠ 0 ∧ G *ᵥ v = μ • v := by sorry
