-- Prove2me | Theorems.Thm_P2M_PI_OmVe_single_mulVec__f4c35258ac1e
-- name    : P2M_PI_OmVe_single_mulVec__f4c35258ac1e
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:06:06.138864+00:00
-- url     : https://prove2.me/theorems/a2cd46ee-08aa-4a59-8542-6a154edc0d5a
-- title:
--   P2 M PI Om Ve single mul Vec  f4c35258ac1e: P2 M PI Om Ve single mul Vec  f4c35258ac1e
-- statement:
--   The P2 M PI Om Ve single mul Vec  f4c35258ac1e construction uses the P2 M PI Om Ve single mul Vec  f4c35258ac1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/SingleMulVec.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/SingleMulVec.lean#L48-L54

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_SingleMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmVe
open PI.VolStabSW Matrix
variable {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)

theorem P2M_PI_OmVe_single_mulVec__f4c35258ac1e {a : ℕ} (i₀ : Fin a) (v : Fin a → K) :
    (Matrix.single i₀ i₀ (1 : K)) *ᵥ v = Pi.single i₀ (v i₀) := by sorry

alias «PI».«OmVe».«single_mulVec'» := P2M_PI_OmVe_single_mulVec__f4c35258ac1e
