-- Prove2me | Theorems.Thm_PI_LocMassTypW_WCoreP_affine_sol
-- name    : PI.LocMassTypW.WCoreP.affine_sol
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:35:53.199163+00:00
-- url     : https://prove2.me/theorems/b25bec80-9fe7-49b9-8c9f-742a0cb82e58
-- title:
--   WCore P: affine sol
-- statement:
--   The WCore P construction uses the affine sol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalMassType/TransitiveOverLocalRings.lean#L177-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalMassType/TransitiveOverLocalRings.lean#L177-L195

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_WCoreDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_TransitiveOverLocalRings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocMassTypW PI.LocMassTypW.WCoreP
open Matrix Module

theorem PI.LocMassTypW.WCoreP.affine_sol {R : Type*} [CommRing R] {n m : ℕ} (A0 A B0 B : Matrix (Fin n) (Fin m) R)
    (L0 M : Matrix (Fin m) (Fin n) R) (hL0 : L0 * A0 = 1) (hM : M * B = 1)
    (hC' : B0ᵀ * A0 = Bᵀ * A) (X : Matrix (Fin n) (Fin n) R) :
    (k1 A B0 B L0 M + (1 - Mᵀ * Bᵀ) * X * (1 - A0 * L0)) * A0 = A ∧
      Bᵀ * (k1 A B0 B L0 M + (1 - Mᵀ * Bᵀ) * X * (1 - A0 * L0)) = B0ᵀ := by sorry
