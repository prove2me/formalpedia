-- Prove2me | Theorems.Thm_P2M_GlobalTheory_BK_eval__toHat_eq_iff_7e88105c9732
-- name    : P2M_GlobalTheory_BK_eval__toHat_eq_iff_7e88105c9732
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:38:07.642481+00:00
-- url     : https://prove2.me/theorems/1390b119-c468-4eb4-9f8b-0241c7021960
-- title:
--   P2 M Global Theory BK eval  to Hat eq iff 7e88105c9732: P2 M Global Theory BK eval  to Hat eq iff 7e88105c9732
-- statement:
--   The P2 M Global Theory BK eval  to Hat eq iff 7e88105c9732 construction uses the P2 M Global Theory BK eval  to Hat eq iff 7e88105c9732 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/SndDualLiftAlgebraMap.lean#L436-L441
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/SndDualLiftAlgebraMap.lean#L436-L441

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DerivationMemPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ)
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
variable [NeZero e] [CompleteSpace K]
variable {O K}

theorem P2M_GlobalTheory_BK_eval__toHat_eq_iff_7e88105c9732 (m : ℕ) (f : Rpi O K l e) (g : invL l (A O K)) :
    AdicCompletion.evalₐ _ m (toHat O K l e f) = Ideal.Quotient.mk _ g ↔
      ∃ h ∈ Rpi O K l e, (f : K⟦X⟧) - g = E K l e ^ m * h := by sorry

alias «GlobalTheory».«BK».«evalₐ_toHat_eq_iff» := P2M_GlobalTheory_BK_eval__toHat_eq_iff_7e88105c9732
