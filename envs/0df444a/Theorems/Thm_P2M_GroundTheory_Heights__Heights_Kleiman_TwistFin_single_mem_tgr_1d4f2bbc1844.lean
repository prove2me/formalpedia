-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_single_mem_tgr_1d4f2bbc1844
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_single_mem_tgr_1d4f2bbc1844
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:12:08.128498+00:00
-- url     : https://prove2.me/theorems/e1e60ecf-5a4c-40ea-ad3c-d47176f8ac35
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Twist Fin single mem tgr 1d4f2bbc1844: P2 M Ground Theory Heights  Heights Kleiman Twist Fin single mem tgr 1d4f2bbc1844
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Twist Fin single mem tgr 1d4f2bbc1844 construction uses the P2 M Ground Theory Heights  Heights Kleiman Twist Fin single mem tgr 1d4f2bbc1844 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/PsiOfIsHomogeneous.lean#L63-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/PsiOfIsHomogeneous.lean#L63-L64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_PsiOfIsHomogeneous
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
open MvPolynomial AddMonoidAlgebra
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.TwistFin
variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω)
variable (S : Type u) [CommRing S] [Algebra S Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_single_mem_tgr_1d4f2bbc1844 (c k : ℤ) (ω : Ω) : (single (c, k) ω : LA Ω) ∈ tgr c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwistFin».«single_mem_tgr» := P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_single_mem_tgr_1d4f2bbc1844
