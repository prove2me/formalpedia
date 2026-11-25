-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_eval__eq_sum_degree_5c698ff6417a
-- name    : P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_eval__eq_sum_degree_5c698ff6417a
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:21:17.878849+00:00
-- url     : https://prove2.me/theorems/d1367316-2ec2-5548-814d-957611f45b60
-- title:
--   P2 M Ground Theory Heights  Heights Incidence Zero Locus eval  eq sum degree 5c698ff6417a: P2 M Ground Theory Heights  Heights Incidence Zero Locus eval  eq sum degree 5c698ff6417a
-- statement:
--   The P2 M Ground Theory Heights  Heights Incidence Zero Locus eval  eq sum degree 5c698ff6417a construction uses the P2 M Ground Theory Heights  Heights Incidence Zero Locus eval  eq sum degree 5c698ff6417a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PIncidenceZeroLocus.lean#L46-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PIncidenceZeroLocus.lean#L46-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus
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
open GroundTheory.Heights₂.Heights.IncidenceZeroLocus

theorem P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_eval__eq_sum_degree_5c698ff6417a {R S : Type*} [CommSemiring R] [CommSemiring S] {n N : ℕ} (g : R →+* S)
    (x : Fin n → S) (p : MvPolynomial (Fin n) R) (hp : p.IsHomogeneous N) :
    eval₂ g x p = ∑ f : ((Finset.univ : Finset (Fin n)).finsuppAntidiag N),
      g (coeff (f : Fin n →₀ ℕ) p) * ∏ j, x j ^ (f : Fin n →₀ ℕ) j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IncidenceZeroLocus».«eval₂_eq_sum_degree» := P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_eval__eq_sum_degree_5c698ff6417a
