-- Prove2me | Theorems.Thm_RelaxationMethod_ConvexDomain_lemma1_case1
-- name    : RelaxationMethod.ConvexDomain.lemma1_case1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:50:06.503987+00:00
-- url     : https://prove2.me/theorems/d8985e7a-de54-49be-99d6-efbb11d3ca10
-- title:
--   Lemma 1, Case 1 — a Fejér-monotone sequence w.r.t. a full-dimensional set converges
-- statement:
--   Let $A \subseteq E_n$ be a set of dimension $n$, i.e. $A$ is contained in no hyperplane (its affine span is $E_n$). If the sequence $\{q_\nu\}$ is Fejér-monotone with respect to $A$, then it converges to a point:
--   $$\exists\, l \in E_n: \quad \lim_{\nu\to\infty} q_\nu = l.$$
--
--   This is the convergence tool behind Theorems 1 and 3 of the paper.
--
--   **Formalization Note** The paper states Lemma 1 for "the polytope $A$" of (1.4), assumed of dimension $r$, and in §10 applies Case 1 to a closed bounded convex set. We state it for an arbitrary set $A$ whose affine span is the whole space, which is exactly what that application requires; "dimension $n$" is rendered as `affineSpan ℝ A = ⊤`.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), p. 397, Lemma 1, Case 1 (proof p. 398)

import Mathlib
import Definitions.Def_RelaxationMethod_Shared_FejerMonotone
open Filter Topology

namespace RelaxationMethod.ConvexDomain

/-- Lemma 1, Case 1, p. 397: a sequence that is Fejér-monotone with respect to a set `A` of
dimension `n` (its affine span is the whole space `E_n`) converges to a point. Stated for an
arbitrary set `A`; the paper states it for the polytope (1.4) and applies it in §10 to a closed
bounded convex set. -/
theorem lemma1_case1 {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hspan : affineSpan ℝ A = ⊤) (q : ℕ → EuclideanSpace ℝ (Fin n))
    (hq : RelaxationMethod.Shared.IsFejerMonotone A q) :
    ∃ l : EuclideanSpace ℝ (Fin n), Tendsto q atTop (𝓝 l) := by sorry

end RelaxationMethod.ConvexDomain
