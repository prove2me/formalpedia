-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_mkF_chartMonomial_mul_chartPow_10a98fec4d52
-- name    : P2M_GroundTheory_Heights__Heights_SectionCycle_mkF_chartMonomial_mul_chartPow_10a98fec4d52
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:36:51.800525+00:00
-- url     : https://prove2.me/theorems/9e71e2d0-8412-45c7-8121-d32c4cfe7026
-- title:
--   P2 M Ground Theory Heights  Heights Section Cycle mk F chart Monomial mul chart Pow 10a98fec4d52: P2 M Ground Theory Heights  Heights Section Cycle mk F chart Monomial mul chart Pow 10a98fec4d52
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Cycle mk F chart Monomial mul chart Pow 10a98fec4d52 construction uses the P2 M Ground Theory Heights  Heights Section Cycle mk F chart Monomial mul chart Pow 10a98fec4d52 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L257-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L257-L264

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SectionCycle
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {P : ArithVariety n} (D : AddBlockData P)
variable {d : ι → ℕ} {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}

theorem P2M_GroundTheory_Heights__Heights_SectionCycle_mkF_chartMonomial_mul_chartPow_10a98fec4d52 (hd : ∀ k, 0 ≤ (d k : ℤ) + D.deg k)
    {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) :
    P.mkF (chartMonomial c d) * P.chartPow c D.deg =
      P.mkF (chartMonomial c fun k ↦ ((d k : ℤ) + D.deg k).toNat) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionCycle».«mkF_chartMonomial_mul_chartPow» := P2M_GroundTheory_Heights__Heights_SectionCycle_mkF_chartMonomial_mul_chartPow_10a98fec4d52
