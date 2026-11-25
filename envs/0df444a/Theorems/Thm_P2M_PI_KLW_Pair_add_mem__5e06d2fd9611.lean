-- Prove2me | Theorems.Thm_P2M_PI_KLW_Pair_add_mem__5e06d2fd9611
-- name    : P2M_PI_KLW_Pair_add_mem__5e06d2fd9611
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:56:39.311607+00:00
-- url     : https://prove2.me/theorems/aa290460-6bd5-4aec-a621-0d731b5ce27e
-- title:
--   P2 M PI KLW Pair add mem  5e06d2fd9611: P2 M PI KLW Pair add mem  5e06d2fd9611
-- statement:
--   The P2 M PI KLW Pair add mem  5e06d2fd9611 construction uses the P2 M PI KLW Pair add mem  5e06d2fd9611 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/PairOfEps.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/PairOfEps.lean#L20-L24

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairOfEps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.Pair
open PI.KLW

theorem P2M_PI_KLW_Pair_add_mem__5e06d2fd9611 {K : Type} [Field K] [NumberField K] {c : K →+* K} {p : ℕ} {ι : Type}
    [Fintype ι] {L : Set (ι → K)} (hL : Unimod K c p L) {a b : ι → K} (ha : a ∈ L) (hb : b ∈ L) :
    a + b ∈ L := by sorry

alias «PI».«KLW».«Pair».«add_mem'» := P2M_PI_KLW_Pair_add_mem__5e06d2fd9611
