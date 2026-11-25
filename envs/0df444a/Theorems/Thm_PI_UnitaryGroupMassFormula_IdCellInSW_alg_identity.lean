-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_IdCellInSW_alg_identity
-- name    : PI.UnitaryGroupMassFormula.IdCellInSW.alg_identity
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:38:48.155252+00:00
-- url     : https://prove2.me/theorems/73dfe5ae-58dc-4157-aa08-767828c87626
-- title:
--   Id Cell In SW: alg identity
-- statement:
--   The Id Cell In SW construction uses the alg identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdentityCellTrace/AlgIdentity.lean#L15-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdentityCellTrace/AlgIdentity.lean#L15-L45

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdentityCellTrace_ExistsSmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdentityCellTrace_AlgIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.IdCellInSW
variable {E : Type} [Field E] [StarRing E] {r : ℕ}

theorem PI.UnitaryGroupMassFormula.IdCellInSW.alg_identity (α α' β β' : Fin r → E) (G s : Fin r → Fin r → E)
    (hs : ∀ a b, G a b + s a b + star (s b a) = 0) :
    (∑ a, α' a * star (β a)) + (∑ a, star (α a) * β' a) +
      (∑ a, ∑ b, star (α a) * (α' b * G a b)) +
      (∑ a, (-β' a + ∑ b, s a b * α' b) * star (α a)) +
      (∑ a, star (-β a + ∑ b, s a b * α b) * α' a) = 0 := by sorry
