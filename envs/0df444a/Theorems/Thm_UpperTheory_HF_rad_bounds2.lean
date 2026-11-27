-- Prove2me | Theorems.Thm_UpperTheory_HF_rad_bounds2
-- name    : UpperTheory.HF.rad_bounds2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:44:59.924923+00:00
-- url     : https://prove2.me/theorems/0f530c5e-75ab-598a-a68f-bf4402ccc2ea
-- title:
--   HF: rad bounds2
-- statement:
--   The HF construction uses the rad bounds2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/RadBounds2.lean#L13-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/RadBounds2.lean#L13-L86

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LogRdSum
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MemRam
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RadBounds
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_NormDiffEK
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RdLower
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RadBounds2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.rad_bounds2 :
    ∀ {φ : Frame} (H : HostAx φ), (∀ α β : ℝ, 0 ≤ α → 0 ≤ β → ∑ l ∈ H.ram, (α * H.vdH l + β) * Real.log l ≤ (α + 2 * β) * Real.log H.rd) ∧ (H.d : ℝ) ≤ H.rd ^ 2 ∧ H.d ^ (2 * φ.ord) ∣ (discr H.E).natAbs ∧ 1 / 2 * Real.log H.d ≤ Real.log H.rd ∧ H.ram.card ≤ H.small.card + 2 ∧ ∀ (M : ℕ) (L : ℝ), 0 < M → 0 ≤ L → Real.log M ≤ 30 * L → Real.log H.rd ≤ L / 100 → ((((discr H.E).natAbs * M).primeFactors.card : ℕ) : ℝ) ≤ 44 * L := by sorry
