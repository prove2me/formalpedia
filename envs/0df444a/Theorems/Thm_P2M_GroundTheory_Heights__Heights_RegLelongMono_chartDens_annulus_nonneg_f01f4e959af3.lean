-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongMono_chartDens_annulus_nonneg_f01f4e959af3
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongMono_chartDens_annulus_nonneg_f01f4e959af3
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:16:49.553746+00:00
-- url     : https://prove2.me/theorems/9ed6b053-9b89-4c11-b168-e1717a11b33a
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Mono chart Dens annulus nonneg f01f4e959af3: P2 M Ground Theory Heights  Heights Reg Lelong Mono chart Dens annulus nonneg f01f4e959af3
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Mono chart Dens annulus nonneg f01f4e959af3 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Mono chart Dens annulus nonneg f01f4e959af3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongMono.lean#L16-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongMono.lean#L16-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLelongAnnulus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongMono
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.RegLelongMono
variable {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (d + 1)) (Fin n) ℂ}

theorem P2M_GroundTheory_Heights__Heights_RegLelongMono_chartDens_annulus_nonneg_f01f4e959af3 (hL : RegLogDensNonneg.Statement) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε)
    (x : Fin n → ℂ) {r s : ℝ} (hr : 0 < r) (y : Fin (d + 1) → ℂ) :
    0 ≤ chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1)
      (vecCons (logReg u ε) fun _ => logDistSq x) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongMono».«chartDens_annulus_nonneg» := P2M_GroundTheory_Heights__Heights_RegLelongMono_chartDens_annulus_nonneg_f01f4e959af3
