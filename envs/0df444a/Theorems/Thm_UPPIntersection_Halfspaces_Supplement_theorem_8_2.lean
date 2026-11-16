-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_Supplement_theorem_8_2
-- name    : UPPIntersection.Halfspaces.Supplement.theorem_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:03:58.44519+00:00
-- url     : https://prove2.me/theorems/4f34ae47-93b6-4016-940f-2030216c5bcf
-- title:
--   Theorem 8.2 — optimality of Theorem 5.1 for strong sign representations outside an $\varepsilon$-band
-- statement:
--   For all $\varepsilon>0$, $k\ge2$ and sufficiently large $d$ there are a dimension $r$ and measurable functions $f,g:(S^{d-1})^k\to\mathbb R^r$ such that $\|f(x)\|_2,\|g(x)\|_2\le1$ for every $x$,
--   $$Q_k(\dots,\langle x_i,y_i\rangle,\dots)\cdot\langle f(x),g(y)\rangle>0\qquad\text{for all }x,y\in(S^{d-1})^k\text{ with }\min_{i\in[k]}|\langle x_i,y_i\rangle|>\varepsilon,$$
--   and
--   $$\mathbb E\big[|\langle f(X),g(Y)\rangle|\big]=2^{-\Theta(d)}$$
--   for independent uniformly random $X,Y\in(S^{d-1})^k$.
--
--   Hence Theorem 5.1 is essentially tight also for arrangements that strongly sign-represent $Q_k$ away from the coordinate hyperplanes.
--
--   **Formalization Note** $2^{-\Theta(d)}$ is encoded as $2^{-bd}\le\mathbb E|\langle f(X),g(Y)\rangle|\le2^{-ad}$ with constants $a,b>0$; the constants and the threshold on $d$ are chosen once for all $\varepsilon$ and $k$. The dimension $r$ may depend on $\varepsilon,k,d$.
--
--   Differences from the source:
--   - reading: for all ε > 0, k ≥ 2 and sufficiently large d, E|⟨f(X),g(Y)⟩| = 2^{−Θ(d)} → constants a, b > 0 and threshold d₀ chosen before ε and k, with 2^{−bd} ≤ E ≤ 2^{−ad} for every ε > 0, k ≥ 2 and d ≥ d₀; reason: the source leaves open whether the Θ-constants and the threshold may depend on ε and k; the stronger, uniform reading is taken (the mixing on p. 31 puts E between m₀/2 and 5m₀/4 for the k-independent m₀ of Theorem 8.1)
--   - encoding: min_{i∈[k]} |⟨x_i,y_i⟩| > ε → ε < |⟨x_i,y_i⟩| for every i; reason: equivalent, since k ≥ 2 makes the minimum over a nonempty index set
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 31, Theorem 8.2 (proof on p. 31, using Theorem 8.1 and the construction in the proof of Lemma 8.4); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_UPPIntersection_Halfspaces_Sphere
import Definitions.Def_UPPIntersection_Halfspaces_Polynomials

open MeasureTheory

namespace UPPIntersection.Halfspaces.Supplement

/-- Bun–Juvekar, Theorem 8.2 (p. 31). For all `ε > 0`, `k ≥ 2` and sufficiently large `d` there are a
dimension `r` and measurable `f, g : (S^{d-1})^k → ℝ^r` with `‖f(x)‖₂, ‖g(x)‖₂ ≤ 1`, with
`Q_k(…, ⟨x_i, y_i⟩, …) · ⟨f(x), g(y)⟩ > 0` whenever `min_i |⟨x_i, y_i⟩| > ε`, and with
`E|⟨f(X), g(Y)⟩| = 2^{-Θ(d)}`: here `2^{-b d} ≤ E|⟨f(X), g(Y)⟩| ≤ 2^{-a d}` with constants `a, b > 0`
and threshold `d₀` independent of `ε` and `k`. -/
theorem theorem_8_2 : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ d₀ : ℕ, ∀ ε : ℝ, 0 < ε → ∀ k : ℕ, 2 ≤ k →
    ∀ d ≥ d₀, ∃ (r : ℕ) (f g : (Fin k → Sph d) → EuclideanSpace ℝ (Fin r)),
      Measurable f ∧ Measurable g ∧ (∀ x, ‖f x‖ ≤ 1) ∧ (∀ y, ‖g y‖ ≤ 1) ∧
      (∀ x y : Fin k → Sph d,
        (∀ i, ε < |inner ℝ (x i : EuclideanSpace ℝ (Fin d)) (y i)|) →
        0 < orthantQ (fun i => inner ℝ (x i : EuclideanSpace ℝ (Fin d)) (y i)) *
          inner ℝ (f x) (g y)) ∧
      (2 : ℝ) ^ (-(b * d)) ≤ ∫ p : (Fin k → Sph d) × (Fin k → Sph d), |inner ℝ (f p.1) (g p.2)|
          ∂((sphereLawPow d k).prod (sphereLawPow d k)) ∧
      ∫ p : (Fin k → Sph d) × (Fin k → Sph d), |inner ℝ (f p.1) (g p.2)|
          ∂((sphereLawPow d k).prod (sphereLawPow d k)) ≤ (2 : ℝ) ^ (-(a * d)) := by sorry

end UPPIntersection.Halfspaces.Supplement
