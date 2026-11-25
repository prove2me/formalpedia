-- Prove2me | Theorems.Thm_PI_TwNormLat_W_combinationEquiv_inv_mem_unipotentFlagGroup
-- name    : PI.TwNormLat.W.combinationEquiv_inv_mem_unipotentFlagGroup
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:31:15.531641+00:00
-- url     : https://prove2.me/theorems/091766d0-0ee5-4bd8-9c31-c7f85a7529c7
-- title:
--   W: combination Equiv inv mem unipotent Flag Group
-- statement:
--   The W construction uses the combination Equiv inv mem unipotent Flag Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedNormLattice/CombinationEquivInvMemUnipotentFlagGroup.lean#L144-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedNormLattice/CombinationEquivInvMemUnipotentFlagGroup.lean#L144-L149

import Definitions.Def_Formalism_PeriodIntegrals_TwNormLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_CombinationEquivInvMemUnipotentFlagGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwNormLat PI.TwNormLat.W
variable {K : Type} [Field K] {n : ℕ}

theorem PI.TwNormLat.W.combinationEquiv_inv_mem_unipotentFlagGroup {N c : ℕ} {b : Fin (N + c) → Fin (N + c) → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0)
    (h1 : ∀ l : Fin (N + c), N ≤ l.1 → b l l = 1) (ha : ∀ hN : N < N + c, b ⟨N, hN⟩ = Pi.single ⟨N, hN⟩ 1) :
    (combE hb hd)⁻¹ ∈ Loc.R1 K N c := by sorry
