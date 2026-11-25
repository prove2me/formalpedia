-- Prove2me | Theorems.Thm_PositivityTheory_CW_CommutatorAdjointLower_Z_eq
-- name    : PositivityTheory.CW.CommutatorAdjointLower.Z_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:49:45.978354+00:00
-- url     : https://prove2.me/theorems/b084da47-f542-56df-a2ef-83e3eec9b020
-- title:
--   Commutator Adjoint Lower: Z eq
-- statement:
--   The Commutator Adjoint Lower construction uses the Z eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/IdentityFiltrationBound.lean#L19-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/IdentityFiltrationBound.lean#L19-L36

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_IdentityFiltrationBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.CommutatorAdjointLower
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem PositivityTheory.CW.CommutatorAdjointLower.Z_eq (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ V} (hE : IsGlRep E) (a b : Fin n) :
    Z ε E a b = ∑ c, ((if ε c = ε a then E a c * E c b + E c b * E a c else 0) -
      (if ε c = ε b then E a c * E c b + E c b * E a c else 0)) := by sorry
