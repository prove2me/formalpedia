-- Prove2me | Theorems.Thm_TeschlODE_Stability_local_flow
-- name    : TeschlODE.Stability.local_flow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T13:13:27.085693+00:00
-- url     : https://prove2.me/theorems/1cc0b220-2b54-4f49-8da6-22e6ff207906
-- title:
--   Theorem 6.1 — the maximal flow exists, $W$ is open, $\Phi \in C^k(W, M)$, flow property (6.11)
-- statement:
--   Let $M \subseteq \mathbb{R}^n$ be open, $k \ge 1$, and $f \in C^k(M, \mathbb{R}^n)$. Then there are intervals $I_x$ and a map $\Phi$ such that $\Phi$ is the flow of $\dot x = f(x)$ on $M$ with maximal intervals $I_x$ (for every $x \in M$, $\Phi(\cdot, x)$ is the unique maximal integral curve at $x$, and $0 \in I_x$), and moreover:
--
--   - $\Phi(\cdot, x) \in C^k(I_x, M)$ for every $x \in M$;
--   - the set $W = \{(t, x) : x \in M,\ t \in I_x\}$ of (6.8) is open in $\mathbb{R} \times \mathbb{R}^n$;
--   - $\Phi \in C^k(W, M)$;
--   - $\Phi$ is a local flow:
--   $$\Phi(0, x) = x, \qquad \Phi(t + s, x) = \Phi(t, \Phi(s, x)), \qquad x \in M,\ s, t + s \in I_x . \qquad (6.11)$$
--
--   This is the book's standing construction for Chapters 6–13: every later statement is about this $\Phi$.
--
--   **Formalization Note.** $\Phi(0,x) = x$, $0 \in I_x$, the values in $M$ and the uniqueness/maximality of $\Phi(\cdot, x)$ are part of `IsMaximalFlow`. In (6.11) the statement also records $t \in I_{\Phi(s,x)}$, which the book states just before the theorem ((6.10): $I_{\Phi(s,x)} = I_x - s$) and which is what makes the right-hand side meaningful. $C^k$ is `ContDiffOn ℝ k` with $k \in \mathbb{N}$, $k \ge 1$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 189, Theorem 6.1

import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve
import Definitions.Def_TeschlODE_Stability_IsMaximalFlow

namespace TeschlODE.Stability

theorem local_flow {n k : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hk : 1 ≤ k)
    (hf : ContDiffOn ℝ k f M) :
    ∃ (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
      (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      IsMaximalFlow f M I Φ ∧
      (∀ x ∈ M, ContDiffOn ℝ k (fun t => Φ t x) (I x)) ∧
      IsOpen {p : ℝ × EuclideanSpace ℝ (Fin n) | p.2 ∈ M ∧ p.1 ∈ I p.2} ∧
      ContDiffOn ℝ k (fun p : ℝ × EuclideanSpace ℝ (Fin n) => Φ p.1 p.2)
        {p : ℝ × EuclideanSpace ℝ (Fin n) | p.2 ∈ M ∧ p.1 ∈ I p.2} ∧
      ∀ x ∈ M, ∀ s t : ℝ, s ∈ I x → t + s ∈ I x →
        t ∈ I (Φ s x) ∧ Φ (t + s) x = Φ t (Φ s x) := by sorry

end TeschlODE.Stability
