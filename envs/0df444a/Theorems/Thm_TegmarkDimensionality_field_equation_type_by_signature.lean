-- Prove2me | Theorems.Thm_TegmarkDimensionality_field_equation_type_by_signature
-- name    : TegmarkDimensionality.field_equation_type_by_signature
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T11:12:17.412468+00:00
-- url     : https://prove2.me/theorems/10722f0c-784e-43f6-9607-398b26de7e91
-- title:
--   Type of the covariant field equations in an $(n+m)$-dimensional spacetime
-- statement:
--   Let $n,m\ge0$ and let $g$ be a real symmetric $(n+m)\times(n+m)$ matrix (a spacetime metric at a point) with exactly $m$ positive and $n$ negative eigenvalues, counted with multiplicity. Then $g$ is invertible. The covariant field equations $g^{\mu\nu}\partial_\mu\partial_\nu u+(\text{lower order})=0$ (wave, Klein–Gordon, …) have coefficient matrix $A=g^{-1}$, and their type is determined by $(n,m)$:
--
--   $$
--   \begin{aligned}
--   A\ \text{elliptic}&\iff n=0\ \text{or}\ m=0,\\
--   A\ \text{hyperbolic}&\iff n=1\ \text{or}\ m=1,\\
--   A\ \text{ultrahyperbolic}&\iff n\ge2\ \text{and}\ m\ge2.
--   \end{aligned}
--   $$
--
--   This is the paper's classification of spacetimes by the causal structure of their field equations (Figure 1). Only hyperbolic equations admit well-posed initial-value problems, so this result singles out $m=1$ (and the tachyonic mirror case $n=1$).
--
--   **Formalization Note** The eigenvalue counts and the three types are those of the definition `tegmark_pde_classification`. The metric is taken at a single point and $g^{-1}$ is the matrix inverse.
-- source:
--   M. Tegmark, *On the dimensionality of spacetime*, Class. Quantum Grav. 14 (1997) L69–L75, https://doi.org/10.1088/0264-9381/14/4/002, p. L73 (second paragraph: 'the matrix A will clearly have the same eigenvalues as the metric tensor') and Figure 1

import Mathlib
import Definitions.Def_tegmark_pde_classification

namespace TegmarkDimensionality

/-- In an `(n+m)`-dimensional spacetime whose metric `g` has `m` positive (time-like)
and `n` negative (space-like) eigenvalues, the covariant field equations
`g^{μν} ∂_μ ∂_ν u + (lower order) = 0`, whose coefficient matrix is `g⁻¹`, are elliptic iff
`n = 0` or `m = 0`, hyperbolic iff `n = 1` or `m = 1`, and ultrahyperbolic iff `n ≥ 2` and
`m ≥ 2`. -/
theorem field_equation_type_by_signature (n m : ℕ)
    (g : Matrix (Fin (n + m)) (Fin (n + m)) ℝ) (hg : g.IsSymm)
    (hpos : numPosEigenvalues g = m) (hneg : numNegEigenvalues g = n) :
    (IsElliptic g⁻¹ ↔ (n = 0 ∨ m = 0)) ∧
      (IsHyperbolic g⁻¹ ↔ (n = 1 ∨ m = 1)) ∧
      (IsUltrahyperbolic g⁻¹ ↔ (2 ≤ n ∧ 2 ≤ m)) := by sorry

end TegmarkDimensionality
