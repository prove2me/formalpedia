-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_div_eq_0873e1843d53
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_div_eq_0873e1843d53
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:42:21.766262+00:00
-- url     : https://prove2.me/theorems/5b2be107-a687-5cd4-b620-0244a9767920
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mem of div eq 0873e1843d53: P2 M Ground Theory Heights  Heights Kleiman mem of div eq 0873e1843d53
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mem of div eq 0873e1843d53 construction uses the P2 M Ground Theory Heights  Heights Kleiman mem of div eq 0873e1843d53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationPoint.lean#L66-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationPoint.lean#L66-L84

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_div_eq_0873e1843d53 (hj : x j ≠ 0) {pp : Ideal (Poly S N)} [hpp : pp.IsPrime]
    (hle : primeOf (S := S) x ≤ pp) (hX : (X j : Poly S N) ∉ pp) {f s' G s : Poly S N} {e D : ℕ}
    (hf : f.IsHomogeneous e) (hs' : s' ∈ monos {j}) (hs'e : s'.IsHomogeneous e) (hG : G ∈ pp)
    (hGD : G.IsHomogeneous D) (hs : s ∈ monos {j}) (hsD : s.IsHomogeneous D)
    (h : aeval x f / aeval x s' = aeval x G / aeval x s) : f ∈ pp := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mem_of_div_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_div_eq_0873e1843d53
