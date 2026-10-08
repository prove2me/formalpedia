-- Prove2me | Theorems.Thm_RegretMatching_Approach_blackwell_procedure
-- name    : RegretMatching.Approach.blackwell_procedure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:16.972976+00:00
-- url     : https://prove2.me/theorems/fefa6b2f-c0e6-47f1-b237-606d3ea84762
-- title:
--   BLACKWELL'S APPROACHABILITY THEOREM (§3), p. 1135, 'Moreover' part — the Blackwell procedure drives dist(D_t, 𝒞) to 0 a.s.
-- statement:
--   Let a decision-maker have a finite nonempty action set $A$ and an opponent a finite nonempty action set $B$, let $L$ be finite and $v:A\times B\to\mathbb R^L$ a vector payoff. Let $\mathcal C\subseteq\mathbb R^L$ be nonempty, closed and convex, with support function $w_{\mathcal C}(\lambda)=\sup\{\lambda\cdot c: c\in\mathcal C\}\in(-\infty,+\infty]$. Suppose that for every $\lambda\in\mathbb R^L$ a mixed strategy $q_\lambda\in\Delta(A)$ satisfies Blackwell's condition (3.2):
--   $$\lambda\cdot v(q_\lambda,b)\le w_{\mathcal C}(\lambda)\qquad\text{for all }b\in B,$$
--   where $v(q,b)=\sum_{a}q(a)v(a,b)$. For $x\in\mathbb R^L$ let $F(x)$ be the point of $\mathcal C$ closest to $x$, and $\lambda(x)=x-F(x)$.
--
--   Let the decision-maker use the **Blackwell procedure**: at time $t+1$ (for $t\ge1$) play $q_{\lambda(D_t)}$ if $D_t\notin\mathcal C$, and play arbitrarily otherwise (and at time $1$), where $D_t=\frac1t\sum_{\tau\le t}v(a_\tau,b_\tau)$. Let the opponent use any procedure, possibly depending on the whole history of play, and let the two randomize independently given the history. Then, almost surely,
--   $$\operatorname{dist}(D_t,\mathcal C)\longrightarrow0\qquad(t\to\infty).$$
--
--   In the proof of Theorem A this is applied with $A=S^i$, $B=S^{-i}$, $\mathcal C=\mathbb R^L_-$.
--
--   **Formalization Note.** (3.2) is encoded without an extended-real support function: $\lambda\cdot v(q_\lambda,b)\le M$ for every real upper bound $M$ of $\{\lambda\cdot c: c\in\mathcal C\}$; this is vacuous exactly when $w_{\mathcal C}(\lambda)=+\infty$. The choice $\lambda\mapsto q_\lambda$ and the closest-point map $F$ are given as functions with the stated properties ($F$ is then the Euclidean projection, which is unique). Nonemptiness of $\mathcal C$ is implicit on the page (the closest point $F(x)$ must exist) and is stated explicitly. The opponent's procedure is any history-dependent mixed action on $B$; the two players' draws are independent given the history. Histories have length $t+1\ge1$; the procedure is unconstrained at time $1$.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), pp. 1134–1135, BLACKWELL'S APPROACHABILITY THEOREM, (3.2), footnotes 12–14

import Mathlib
import Definitions.Def_RegretMatching_Approach_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Approach

theorem blackwell_procedure
    {A B L : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [Fintype L]
    (v : A → B → EuclideanSpace ℝ L)
    (C : Set (EuclideanSpace ℝ L)) (hCc : IsClosed C) (hCv : Convex ℝ C) (hCne : C.Nonempty)
    (qsel : EuclideanSpace ℝ L → A → ℝ)
    (hqsel : ∀ lam : EuclideanSpace ℝ L, qsel lam ∈ stdSimplex ℝ A ∧
      ∀ (b : B) (M : ℝ), (∀ c ∈ C, inner ℝ lam c ≤ M) →
        inner ℝ lam (∑ a : A, qsel lam a • v a b) ≤ M)
    (F : EuclideanSpace ℝ L → EuclideanSpace ℝ L)
    (hF : ∀ x, F x ∈ C ∧ ∀ c ∈ C, dist x (F x) ≤ dist x c)
    (f : (t : ℕ) → (Fin t → A × B) → A → ℝ)
    (hf : ∀ (t : ℕ) (h : Fin t → A × B), f t h ∈ stdSimplex ℝ A)
    (hfB : ∀ (t : ℕ) (h : Fin (t + 1) → A × B), avgVec v h ∉ C →
      f (t + 1) h = qsel (avgVec v h - F (avgVec v h)))
    (g : (t : ℕ) → (Fin t → A × B) → B → ℝ)
    (hg : ∀ (t : ℕ) (h : Fin t → A × B), g t h ∈ stdSimplex ℝ B)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (play : ℕ → Ω → A × B) (hplay : IsPlay2 f g P play) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℕ => Metric.infDist (avgVec v (hist play (t + 1) ω)) C)
      atTop (𝓝 0) := by sorry

end RegretMatching.Approach
