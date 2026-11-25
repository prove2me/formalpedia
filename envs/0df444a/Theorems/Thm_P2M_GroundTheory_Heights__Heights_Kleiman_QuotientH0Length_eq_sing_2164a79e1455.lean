-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_eq_sing_2164a79e1455
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_eq_sing_2164a79e1455
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:56:04.393112+00:00
-- url     : https://prove2.me/theorems/a6292bd3-3207-5717-8a30-cc3cf3f1467c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length eq sing 2164a79e1455: P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length eq sing 2164a79e1455
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length eq sing 2164a79e1455 construction uses the P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length eq sing 2164a79e1455 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LengthQuotientEqLengthH0.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LengthQuotientEqLengthH0.lean#L88-L91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LengthQuotientEqLengthH0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.QuotientH0Length
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_eq_sing_2164a79e1455 (I : Cech.Idx (support x) 0) : ∃ (a : Fin (N + 1)) (ha : a ∈ support x), I = sing ha := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«QuotientH0Length».«eq_sing» := P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_eq_sing_2164a79e1455
