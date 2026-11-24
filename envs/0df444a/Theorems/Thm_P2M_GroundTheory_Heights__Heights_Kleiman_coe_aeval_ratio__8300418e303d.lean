-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coe_aeval_ratio__8300418e303d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_coe_aeval_ratio__8300418e303d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:25.167148+00:00
-- url     : https://prove2.me/theorems/d8bf38c8-ce46-4b30-b202-966480307638
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman coe aeval ratio  8300418e303d: P2 M Ground Theory Heights  Heights Kleiman coe aeval ratio  8300418e303d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman coe aeval ratio  8300418e303d construction uses the P2 M Ground Theory Heights  Heights Kleiman coe aeval ratio  8300418e303d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationPoint.lean#L132-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationPoint.lean#L132-L135

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_coe_aeval_ratio__8300418e303d (hj : x j ≠ 0) {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) :
    ((aeval (ratio (S := S) hj) f : chartRing S x (singleChart hj)) : Ω) =
      aeval x f / aeval x (X j ^ e : Poly S N) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«coe_aeval_ratio'» := P2M_GroundTheory_Heights__Heights_Kleiman_coe_aeval_ratio__8300418e303d
