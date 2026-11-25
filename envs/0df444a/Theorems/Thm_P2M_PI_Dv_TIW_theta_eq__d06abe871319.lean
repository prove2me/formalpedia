-- Prove2me | Theorems.Thm_P2M_PI_Dv_TIW_theta_eq__d06abe871319
-- name    : P2M_PI_Dv_TIW_theta_eq__d06abe871319
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:55:46.651271+00:00
-- url     : https://prove2.me/theorems/80682a4b-60df-50f9-b111-b80b7d9da1b7
-- title:
--   P2 M PI Dv TIW theta eq  d06abe871319: P2 M PI Dv TIW theta eq  d06abe871319
-- statement:
--   The P2 M PI Dv TIW theta eq  d06abe871319 construction uses the P2 M PI Dv TIW theta eq  d06abe871319 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/TauCentralScalar.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/TauCentralScalar.lean#L30-L33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : GoodSet K G) (s : T.S)

theorem P2M_PI_Dv_TIW_theta_eq__d06abe871319 (M : Module.End K (T.W s)) : theta T s M =
    ∑ y : G, (((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
      LinearMap.trace K (T.W s) (M * T.tau s y⁻¹)) • MonoidAlgebra.of K G y := by sorry

alias «PI».«Dv».«TIW».«theta_eq'» := P2M_PI_Dv_TIW_theta_eq__d06abe871319
