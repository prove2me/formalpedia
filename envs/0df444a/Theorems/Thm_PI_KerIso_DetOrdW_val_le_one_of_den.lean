-- Prove2me | Theorems.Thm_PI_KerIso_DetOrdW_val_le_one_of_den
-- name    : PI.KerIso.DetOrdW.val_le_one_of_den
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:33:19.580738+00:00
-- url     : https://prove2.me/theorems/de9dae6c-4e59-40fa-ad65-b8162cf535c4
-- title:
--   Det Ord W: val le one of den
-- statement:
--   The Det Ord W construction uses the val le one of den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelOrder/ValNatCastEqOne.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelOrder/ValNatCastEqOne.lean#L29-L35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelOrder_ValNatCastEqOne
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
open PI PI.KerIso PI.KerIso.DetOrdW
open IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]

theorem PI.KerIso.DetOrdW.val_le_one_of_den (𝔭 : HeightOneSpectrum (𝓞 K)) {p s : ℕ}
    (hp : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal) (hs : Nat.Coprime s p) {x : K}
    (hx : (s : K) * x ∈ (algebraMap (𝓞 K) K).range) : 𝔭.valuation K x ≤ 1 := by sorry
