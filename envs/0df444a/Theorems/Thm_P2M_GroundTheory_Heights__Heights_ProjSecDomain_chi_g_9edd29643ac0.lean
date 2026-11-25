-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjSecDomain_chi_g_9edd29643ac0
-- name    : P2M_GroundTheory_Heights__Heights_ProjSecDomain_chi_g_9edd29643ac0
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:16:05.101792+00:00
-- url     : https://prove2.me/theorems/c2cf6ec5-67a4-4112-8b3b-f080b82987be
-- title:
--   P2 M Ground Theory Heights  Heights Proj Sec Domain chi g 9edd29643ac0: P2 M Ground Theory Heights  Heights Proj Sec Domain chi g 9edd29643ac0
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Sec Domain chi g 9edd29643ac0 construction uses the P2 M Ground Theory Heights  Heights Proj Sec Domain chi g 9edd29643ac0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjSecDomain.lean#L164-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjSecDomain.lean#L164-L171

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjSecDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjSecDomain
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
open GroundTheory.Heights₂.Heights.ProjSecDomain
variable {n e : ℕ} (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ)
variable {W A}
variable (W A)
variable {W A}
variable (W A)
variable {W A}

theorem P2M_GroundTheory_Heights__Heights_ProjSecDomain_chi_g_9edd29643ac0 (s : S W A) : chi W A (g W A s) = s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjSecDomain».«chi_g» := P2M_GroundTheory_Heights__Heights_ProjSecDomain_chi_g_9edd29643ac0
