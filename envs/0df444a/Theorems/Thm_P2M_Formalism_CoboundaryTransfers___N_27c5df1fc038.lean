-- Prove2me | Theorems.Thm_P2M_Formalism_CoboundaryTransfers___N_27c5df1fc038
-- name    : P2M_Formalism_CoboundaryTransfers___N_27c5df1fc038
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:52:58.552997+00:00
-- url     : https://prove2.me/theorems/267c5182-62cb-464d-9f98-6420bf13e86f
-- title:
--   P2 M Formalism Coboundary Transfers   N 27c5df1fc038: P2 M Formalism Coboundary Transfers   N 27c5df1fc038
-- statement:
--   The P2 M Formalism Coboundary Transfers   N 27c5df1fc038 construction uses the P2 M Formalism Coboundary Transfers   N 27c5df1fc038 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/TorsionKilledCriterionHolds.lean#L96-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/TorsionKilledCriterionHolds.lean#L96-L104

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_TorsionKilledCriterionHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]

theorem P2M_Formalism_CoboundaryTransfers___N_27c5df1fc038 (W : WachMod B M D) (δ : D →ₗ[O] D) (h2 : ∀ y, B.X • δ y = W.γ y - y) :
    ∀ n ∈ W.N, δ n ∈ W.N := by sorry

alias «Formalism».«CoboundaryTransfers».«δ_N» := P2M_Formalism_CoboundaryTransfers___N_27c5df1fc038
