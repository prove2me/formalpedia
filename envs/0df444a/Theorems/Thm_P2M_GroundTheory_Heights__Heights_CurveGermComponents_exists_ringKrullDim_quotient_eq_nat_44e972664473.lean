-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveGermComponents_exists_ringKrullDim_quotient_eq_nat_44e972664473
-- name    : P2M_GroundTheory_Heights__Heights_CurveGermComponents_exists_ringKrullDim_quotient_eq_nat_44e972664473
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:22.654745+00:00
-- url     : https://prove2.me/theorems/6691ce1a-73fd-5aa2-9fef-e6d33e80cd01
-- title:
--   P2 M Ground Theory Heights  Heights Curve Germ Components exists ring Krull Dim quotient eq nat 44e972664473: P2 M Ground Theory Heights  Heights Curve Germ Components exists ring Krull Dim quotient e
-- statement:
--   The P2 M Ground Theory Heights  Heights Curve Germ Components exists ring Krull Dim quotient eq nat 44e972664473 construction uses the P2 M Ground Theory Heights  Heights Curve Germ Components exists ring Krull Dim quotient eq nat 44e972664473 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveGermComponents.lean#L97-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveGermComponents.lean#L97-L110

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalDimDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveGermComponents
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
open MvPolynomial ComplexSets Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.CurveGermComponents
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_CurveGermComponents_exists_ringKrullDim_quotient_eq_nat_44e972664473 (W : Ideal (MvPolynomial (Fin n) ℂ)) [W.IsPrime] :
    ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (e : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CurveGermComponents».«exists_ringKrullDim_quotient_eq_nat» := P2M_GroundTheory_Heights__Heights_CurveGermComponents_exists_ringKrullDim_quotient_eq_nat_44e972664473
