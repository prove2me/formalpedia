-- Prove2me | Theorems.Thm_StochSQP_Vanishing_Supplement_lemma_6
-- name    : StochSQP.Vanishing.Supplement.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:16:43.120394+00:00
-- url     : https://prove2.me/theorems/5891ac26-aa05-4724-beab-e088dc9dff85
-- title:
--   Lemma 6 (used in the proof of Theorem 1) — normal step versus feasibility reduction
-- statement:
--   Let a run satisfy Assumptions 1 and 3 on an open convex set containing its iterates. If $\|J_k^Tz\|_2\ge\sigma_J\|z\|_2$ for all $z\in\mathbb R^m$ and $k\ge k_J$, with $\sigma_J>0$, then some $\kappa_\omega>0$ satisfies
--   $$\|v_k\|_2\le\kappa_\omega\bigl(\|c_k\|_2-\|c_k+J_kv_k\|_2\bigr)\quad(k\ge k_J).$$
--   The constant may depend on this run. This estimate supports merit stabilization in Lemma 8.
--
--   Differences from the source:
--   - generalization: stochastic algorithm context with unbiased finite-variance gradients and independent Hessians → a pathwise algorithm run with the stated deterministic bounds, without probability or moment premises; reason: the statement and proof of this lemma use only the pathwise rules and bounds; every stochastic realization satisfying the source assumptions specializes to this statement
--   - encoding: Euclidean matrix notation and sequence limits → finite Euclidean spaces, adjoints, varying-dimensional isometries, and Tendsto to zero; reason: these express the same vectors, norms, bases and full-sequence limits, including zero-dimensional spaces
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, p. 13, Lemma 6

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Supplement_Geometry

namespace StochSQP.Vanishing.Supplement

open Filter
open scoped InnerProductSpace RealInnerProductSpace Topology

theorem lemma_6
    {n m : ℕ} (P : Problem n m) (A : Params) (R : Run n m)
    (X : Set (E n)) (κH ζH : ℝ)
    (hA : A.Valid) (hP : Assumption1 P A.L A.Γ X)
    (hx : ∀ k, R.x k ∈ X) (hH : Assumption3 P R κH ζH)
    (hrun : IsRun P A R)
    (kJ : ℕ) (σJ : ℝ) (hσ : 0 < σJ) (hJ : RankBound P R kJ σJ) :
    ∃ κω : ℝ, 0 < κω ∧ ∀ k ≥ kJ,
      ‖R.v k‖ ≤ κω * (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖) := by sorry

end StochSQP.Vanishing.Supplement
