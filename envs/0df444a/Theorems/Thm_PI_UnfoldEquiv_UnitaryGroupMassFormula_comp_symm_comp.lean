-- Prove2me | Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_comp_symm_comp
-- name    : PI.UnfoldEquiv.UnitaryGroupMassFormula.comp_symm_comp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:31:19.737726+00:00
-- url     : https://prove2.me/theorems/5c1acdfb-0cf5-5fe5-b0b3-064c6de008bf
-- title:
--   Unitary Group Mass Formula: comp symm comp
-- statement:
--   The Unitary Group Mass Formula construction uses the comp symm comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnfoldingEquivalence/CompSymmComp.lean#L76-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnfoldingEquivalence/CompSymmComp.lean#L76-L80

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_Points
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_CompSymmComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI.UnfoldEquiv PI.UnfoldEquiv.Loc
noncomputable section
open PI PI.UnfoldEquiv PI.UnfoldEquiv.UnitaryGroupMassFormula
variable {k : Type} [CommRing k]

theorem PI.UnfoldEquiv.UnitaryGroupMassFormula.comp_symm_comp {n' n c : ℕ} (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))
    (y : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)) : r.toLinearMap ∘ₗ (r.symm.toLinearMap ∘ₗ y) = y := by sorry
