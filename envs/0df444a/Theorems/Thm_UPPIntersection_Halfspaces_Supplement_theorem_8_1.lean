-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_Supplement_theorem_8_1
-- name    : UPPIntersection.Halfspaces.Supplement.theorem_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:03:30.417404+00:00
-- url     : https://prove2.me/theorems/1380e0d2-f5f4-4490-9f57-89be2bbf26b7
-- title:
--   Theorem 8.1 — optimality of Theorem 5.1: $[0,1]$-valued weak representations of $Q_k$ with $E|f(X)g(Y)|=2^{-\Theta(d)}$
-- statement:
--   For all $k\ge1$ and all sufficiently large $d$ there are measurable functions $f,g:(S^{d-1})^k\to[0,1]$ such that
--   $$Q_k(\dots,\langle x_i,y_i\rangle,\dots)\cdot f(x)\cdot g(y)\ge0\qquad\text{for all }x,y\in(S^{d-1})^k$$
--   and
--   $$\mathbb E\big[|f(X)g(Y)|\big]=2^{-\Theta(d)}$$
--   for independent uniformly random $X,Y\in(S^{d-1})^k$. Here $Q_k(s)=\bigwedge_i\operatorname{sgn}s_i$ if every $s_i\neq0$ and $Q_k(s)=0$ otherwise.
--
--   So the exponentially small average margin of Theorem 5.1 cannot be improved, even for scalar arrangements and weak sign representation everywhere.
--
--   **Formalization Note** $2^{-\Theta(d)}$ is encoded as $2^{-bd}\le\mathbb E|f(X)g(Y)|\le2^{-ad}$ with constants $a,b>0$; the constants and the threshold on $d$ are chosen once for all $k$.
--
--   Differences from the source:
--   - reading: for all k ≥ 1 and sufficiently large d, E|f(X)g(Y)| = 2^{−Θ(d)} → constants a, b > 0 and threshold d₀ chosen before k, with 2^{−bd} ≤ E ≤ 2^{−ad} for every k ≥ 1 and d ≥ d₀; reason: the source leaves open whether the Θ-constants and the threshold may depend on k; the stronger, k-uniform reading is taken (the cap construction on p. 30 depends only on the first coordinate)
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 30, Theorem 8.1 (proof on pp. 30–31); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_UPPIntersection_Halfspaces_Sphere
import Definitions.Def_UPPIntersection_Halfspaces_Polynomials

open MeasureTheory

namespace UPPIntersection.Halfspaces.Supplement

/-- Bun–Juvekar, Theorem 8.1 (p. 30). For all `k ≥ 1` and all sufficiently large `d` there are
measurable `f, g : (S^{d-1})^k → [0,1]` with `Q_k(…, ⟨x_i, y_i⟩, …) · f(x) · g(y) ≥ 0` for all
`x, y ∈ (S^{d-1})^k` and `E|f(X) g(Y)| = 2^{-Θ(d)}` for independent uniform `X, Y`: here
`2^{-b d} ≤ E|f(X) g(Y)| ≤ 2^{-a d}` with constants `a, b > 0` and threshold `d₀` independent of `k`. -/
theorem theorem_8_1 : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ d₀ : ℕ, ∀ k : ℕ, 1 ≤ k → ∀ d ≥ d₀,
    ∃ f g : (Fin k → Sph d) → ℝ, Measurable f ∧ Measurable g ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧ (∀ y, 0 ≤ g y ∧ g y ≤ 1) ∧
      (∀ x y : Fin k → Sph d,
        0 ≤ orthantQ (fun i => inner ℝ (x i : EuclideanSpace ℝ (Fin d)) (y i)) * f x * g y) ∧
      (2 : ℝ) ^ (-(b * d)) ≤ ∫ p : (Fin k → Sph d) × (Fin k → Sph d), |f p.1 * g p.2|
          ∂((sphereLawPow d k).prod (sphereLawPow d k)) ∧
      ∫ p : (Fin k → Sph d) × (Fin k → Sph d), |f p.1 * g p.2|
          ∂((sphereLawPow d k).prod (sphereLawPow d k)) ≤ (2 : ℝ) ^ (-(a * d)) := by sorry

end UPPIntersection.Halfspaces.Supplement
