-- Prove2me | Theorems.Thm_Rudin_ch09_mixed_partials
-- name    : Rudin.ch09_mixed_partials
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:24:55.441863+00:00
-- url     : https://prove2.me/theorems/4dea36eb-e4ff-4f16-b3f3-2a810f9f42c5
-- title:
--   Theorem 9.41 — equality of mixed partial derivatives
-- statement:
--   Let $f$ be defined on an open $E \subseteq \mathbb{R}^2$, suppose $D_1f$, $D_2f$ and $D_{21}f = D_2(D_1f)$ exist at every point of $E$, and suppose $D_{21}f$ is continuous at $(a,b) \in E$. Then $D_{12}f$ exists at $(a,b)$ and $D_{12}f(a,b) = D_{21}f(a,b)$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 9, p. 235, Theorems 9.40 and 9.41

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 9.41: if `D₁f`, `D₂f` and `D₂₁f = D₂(D₁f)` exist on an open set `E ⊆ ℝ²`
and `D₂₁f` is continuous at `(a, b) ∈ E`, then `D₁₂f` exists at `(a, b)` and equals
`D₂₁f (a, b)`. -/
theorem ch09_mixed_partials (E : Set (ℝ × ℝ)) (hE : IsOpen E) (f D1f D2f D21f : ℝ → ℝ → ℝ)
    (h1 : ∀ p ∈ E, HasDerivAt (fun u : ℝ => f u p.2) (D1f p.1 p.2) p.1)
    (h2 : ∀ p ∈ E, HasDerivAt (fun v : ℝ => f p.1 v) (D2f p.1 p.2) p.2)
    (h21 : ∀ p ∈ E, HasDerivAt (fun v : ℝ => D1f p.1 v) (D21f p.1 p.2) p.2)
    (a b : ℝ) (hab : (a, b) ∈ E)
    (hcont : ContinuousAt (fun p : ℝ × ℝ => D21f p.1 p.2) (a, b)) :
    HasDerivAt (fun u : ℝ => D2f u b) (D21f a b) a := by sorry

end Rudin
