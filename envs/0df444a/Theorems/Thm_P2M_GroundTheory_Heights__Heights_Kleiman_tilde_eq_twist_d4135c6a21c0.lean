-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_tilde_eq_twist_d4135c6a21c0
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_tilde_eq_twist_d4135c6a21c0
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:01:45.730393+00:00
-- url     : https://prove2.me/theorems/5fb75419-f492-4fe6-90de-83608bc6b7e5
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman tilde eq twist d4135c6a21c0: P2 M Ground Theory Heights  Heights Kleiman tilde eq twist d4135c6a21c0
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman tilde eq twist d4135c6a21c0 construction uses the P2 M Ground Theory Heights  Heights Kleiman tilde eq twist d4135c6a21c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFiniteSections.lean#L43-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFiniteSections.lean#L43-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFiniteSections
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
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_tilde_eq_twist_d4135c6a21c0 (M : FinGradedSub (S := S) (x := x) Ω) (c : ℤ) (I : Chart x) :
    M.tilde c I = ((M.tildeSys 0).twist (twistSys S x c)).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«tilde_eq_twist» := P2M_GroundTheory_Heights__Heights_Kleiman_tilde_eq_twist_d4135c6a21c0
