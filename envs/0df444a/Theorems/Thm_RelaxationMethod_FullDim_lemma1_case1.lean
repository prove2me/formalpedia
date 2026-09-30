-- Prove2me | Theorems.Thm_RelaxationMethod_FullDim_lemma1_case1
-- name    : RelaxationMethod.FullDim.lemma1_case1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:26:38.595422+00:00
-- url     : https://prove2.me/theorems/c013f162-3182-45d4-a87f-15b68ff2169f
-- title:
--   Lemma 1, Case 1 — a Fejér-monotone sequence converges when $A$ spans $E_n$
-- statement:
--   Let $A$ be a set of points of $E_n$ that is not contained in any hyperplane, i.e. whose affine span is all of $E_n$ (dimension $r = n$). If the sequence $q_0, q_1, \dots$ is Fejér-monotone with respect to $A$ (it lies outside $A$, consecutive terms differ, and $|q_{i+1} - a| \le |q_i - a|$ for every $a \in A$), then it converges: there is a point $l \in E_n$ with
--
--   $$
--   \lim_{\nu\to\infty} q_\nu = l .
--   $$
--
--   This is the convergence engine of the paper: applied to relaxation sequences it gives Agmon's convergence theorem (Theorem 1, Case 1) and is the first step of the finite-termination proof for the reflexion method (Theorem 1, Case 2).
--
--   **Formalization Note** The paper states the lemma for the polytope $A$ of (1.4); we state it for an arbitrary set $A$ whose affine span is the whole space, which contains the paper's case (a nonempty polytope of dimension $n$). "Not contained in any hyperplane" is `affineSpan ℝ A = ⊤`; this also forces $A$ to be nonempty.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), p. 397, Lemma 1, Case 1

import Mathlib
import Definitions.Def_RelaxationMethod_FullDim_RelaxStep
import Definitions.Def_RelaxationMethod_FullDim_FejerMonotone
open Filter Topology

namespace RelaxationMethod.FullDim

/-- Lemma 1, Case 1, p. 397: a sequence that is Fejér-monotone with respect to a set `A` of
dimension `n` (not contained in any hyperplane, `affineSpan ℝ A = ⊤`) converges to a point.
Stated for an arbitrary set `A`, which contains the paper's case of the polytope (1.4). -/
theorem lemma1_case1 {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hr : affineSpan ℝ A = ⊤) (q : ℕ → EuclideanSpace ℝ (Fin n))
    (hq : IsFejerMonotone A q) :
    ∃ l : EuclideanSpace ℝ (Fin n), Tendsto q atTop (𝓝 l) := by sorry

end RelaxationMethod.FullDim
