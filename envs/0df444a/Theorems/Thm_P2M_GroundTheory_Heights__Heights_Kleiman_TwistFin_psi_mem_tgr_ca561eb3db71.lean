-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_psi_mem_tgr_ca561eb3db71
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_psi_mem_tgr_ca561eb3db71
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:25.397801+00:00
-- url     : https://prove2.me/theorems/c26908d7-f809-42e7-b228-2e4a9fabd9bd
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Twist Fin psi mem tgr ca561eb3db71: P2 M Ground Theory Heights  Heights Kleiman Twist Fin psi mem tgr ca561eb3db71
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Twist Fin psi mem tgr ca561eb3db71 construction uses the P2 M Ground Theory Heights  Heights Kleiman Twist Fin psi mem tgr ca561eb3db71 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/PsiOfIsHomogeneous.lean#L69-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/PsiOfIsHomogeneous.lean#L69-L77

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_psi_mem_tgr_ca561eb3db71 (s : Sy S r) : psi η S s ∈ tgr 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwistFin».«psi_mem_tgr» := P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_psi_mem_tgr_ca561eb3db71
