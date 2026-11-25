-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_notMem_of_mem_monos_single_81fb4626dda4
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_notMem_of_mem_monos_single_81fb4626dda4
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:03.297628+00:00
-- url     : https://prove2.me/theorems/fb74a1d5-bebb-4d3e-9a32-5fa4e151f126
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman not Mem of mem monos single 81fb4626dda4: P2 M Ground Theory Heights  Heights Kleiman not Mem of mem monos single 81fb4626dda4
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman not Mem of mem monos single 81fb4626dda4 construction uses the P2 M Ground Theory Heights  Heights Kleiman not Mem of mem monos single 81fb4626dda4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationPoint.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationPoint.lean#L61-L64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
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
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {j : Fin (N + 1)}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_notMem_of_mem_monos_single_81fb4626dda4 {pp : Ideal (Poly S N)} [hpp : pp.IsPrime]
    (hX : (X j : Poly S N) ∉ pp) {s : Poly S N} (hs : s ∈ monos {j}) : s ∉ pp := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«notMem_of_mem_monos_single» := P2M_GroundTheory_Heights__Heights_Kleiman_notMem_of_mem_monos_single_81fb4626dda4
