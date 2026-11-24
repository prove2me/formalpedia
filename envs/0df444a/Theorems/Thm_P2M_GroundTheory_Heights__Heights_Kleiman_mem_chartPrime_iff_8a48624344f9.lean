-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_chartPrime_iff_8a48624344f9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mem_chartPrime_iff_8a48624344f9
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:29.341394+00:00
-- url     : https://prove2.me/theorems/46be5f60-eaa1-468a-825b-cf1e9c2c6f81
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mem chart Prime iff 8a48624344f9: P2 M Ground Theory Heights  Heights Kleiman mem chart Prime iff 8a48624344f9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mem chart Prime iff 8a48624344f9 construction uses the P2 M Ground Theory Heights  Heights Kleiman mem chart Prime iff 8a48624344f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationPoint.lean#L114-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationPoint.lean#L114-L123

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mem_chartPrime_iff_8a48624344f9 (hj : x j ≠ 0) {pp : Ideal (Poly S N)} [pp.IsPrime]
    (hle : primeOf (S := S) x ≤ pp) (hX : (X j : Poly S N) ∉ pp) {a : chartRing S x (singleChart hj)}
    {f s : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) (hs : s ∈ monos {j}) (hse : s.IsHomogeneous e)
    (ha : (a : Ω) = aeval x f / aeval x s) : a ∈ chartPrime pp hj ↔ f ∈ pp := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mem_chartPrime_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_mem_chartPrime_iff_8a48624344f9
