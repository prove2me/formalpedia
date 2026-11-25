-- Prove2me | Theorems.Thm_P2M_PI_KLW_Pair_smul_mem__4f5cbb083064
-- name    : P2M_PI_KLW_Pair_smul_mem__4f5cbb083064
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:54:33.766409+00:00
-- url     : https://prove2.me/theorems/b393236c-479f-4792-853c-f39d0b88a270
-- title:
--   P2 M PI KLW Pair smul mem  4f5cbb083064: P2 M PI KLW Pair smul mem  4f5cbb083064
-- statement:
--   The P2 M PI KLW Pair smul mem  4f5cbb083064 construction uses the P2 M PI KLW Pair smul mem  4f5cbb083064 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/PairOfEps.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/PairOfEps.lean#L14-L18

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

theorem P2M_PI_KLW_Pair_smul_mem__4f5cbb083064 {K : Type} [Field K] [NumberField K] {c : K →+* K} {p : ℕ} {ι : Type}
    [Fintype ι] {L : Set (ι → K)} (hL : Unimod K c p L) {b : ι → K} (hb : b ∈ L) {r : K}
    (hr : Rp K p r) : r • b ∈ L := by sorry

alias «PI».«KLW».«Pair».«smul_mem'» := P2M_PI_KLW_Pair_smul_mem__4f5cbb083064
