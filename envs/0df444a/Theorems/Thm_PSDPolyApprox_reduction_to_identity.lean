-- Prove2me | Theorems.Thm_PSDPolyApprox_reduction_to_identity
-- name    : PSDPolyApprox.reduction_to_identity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:50:53.789724+00:00
-- url     : https://prove2.me/theorems/85f98ee4-e6ab-42d8-bb1b-80ac4b922d7b
-- title:
--   §3, p.4 — reduction to $A=\frac1nI_n$ (Aubrun): the Minkowski average $Q=\frac1n\sum_iS^iPS^{-i}$ is in the centered sandwich, $\operatorname{xc}(Q)\le n\operatorname{xc}(P)$
-- statement:
--   Let $0<\epsilon<1$, let $A$ be a real symmetric $n\times n$ matrix with $\operatorname{Tr}A=1$, and let $P$ be a polytope with
--   $$
--   (1-\epsilon)(\mathcal D-A)\subseteq P\subseteq\mathcal D-A .
--   $$
--   Let $U$ be an orthogonal matrix such that $UAU^{\mathsf T}$ is diagonal (the rotation of the paper; it exists by the spectral theorem), and let $S$ be the permutation matrix of the cycle $(1,2,\dots,n)$. Then the Minkowski average
--   $$
--   Q=\frac1n\sum_{i=1}^n S^i\,(UPU^{\mathsf T})\,S^{-i}
--   $$
--   is a polytope with
--   $$
--   (1-\epsilon)\Bigl(\mathcal D-\tfrac1nI_n\Bigr)\subseteq Q\subseteq\mathcal D-\tfrac1nI_n\qquad\text{and}\qquad \operatorname{xc}(Q)\le n\,\operatorname{xc}(P).
--   $$
--   So a lower bound $e^{c\sqrt n}$ for the centered case $A=\frac1nI_n$ gives the lower bound $e^{c\sqrt n}/n$ for every $A$.
--
--   Differences from the source:
--   - encoding: "By applying a rotation we can assume without loss of generality that A is diagonal", then Q = (1/n) Σ_{i=1}^n S^i P S^{−i} for the rotated P → an explicit orthogonal U with U A Uᵀ diagonal as a hypothesis, and Q = (1/n) Σ_{i=1}^n S^i (U P Uᵀ) S^{−i}, S = (finRotate n).permMatrix ℝ; reason: the WLOG step made explicit; the statement holds for every such U, one of which exists by the spectral theorem; S^{−i} = (S^i)ᵀ
--   - encoding: sets of n × n matrices and the congruence X ↦ M X Mᵀ → their images in ℝ^{n×n} under the flattening Matrix.vec, the congruence acting through the inverse of vec; reason: vec is a linear isomorphism carrying the trace inner product to the dot product; extension complexity is invariant under it (equations are free)
--   - encoding: extension complexity = smallest number of facets of a polytope whose linear image is P (Definition 1) → smallest number of inequalities of an extended formulation of P (ExtensionComplexity.TSP.extensionComplexity); reason: the two minima coincide for polytopes of dimension ≥ 1 (Fiorini et al., J. ACM 2015, Theorem 3, published as ExtensionComplexity.TSP.yannakakis_factorization); for a point or the empty set the inequality count is 0 and never exceeds the facet count, so in those degenerate cases the Lean inequality still implies the paper's
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, §3, p.4 ("Reduction to the case A = 1/n In", argument of G. Aubrun)

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_Polytope
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_PSDPolyApprox_shiftedDensity

open ExtensionComplexity.TSP
open scoped Pointwise Matrix

namespace PSDPolyApprox

/-- **Reduction to the case `A = (1/n)Iₙ`** (argument of G. Aubrun).
Fawzi, arXiv:1811.09649v1, §3, p.4: "Assume P is a polytope such that (1 − ǫ)(D − A) ⊂ P ⊂ D − A
where A is a symmetric matrix of trace equal to one. By applying a rotation we can assume without
loss of generality that A is diagonal. Let S be the permutation matrix for the cycle
(1, 2, . . . , n). … we get (1 − ǫ)(D − 1/n In) ⊂ Q ⊂ D − 1/n In where Q = 1/n Σn i=1 SiPS−i
(Minkowski sum). … If we denote the extension complexity by xc this yields xc(Q) ≤ n xc(P)."

For `0 < ε < 1`, a symmetric `A` with `Tr A = 1`, a polytope `P` with
`(1 − ε)(D − A) ⊆ P ⊆ D − A`, and an orthogonal `U` with `U A Uᵀ` diagonal (the rotation), the
Minkowski average `Q = (1/n) ∑_{i=1}^n Sⁱ (U P Uᵀ) S⁻ⁱ`, `S` the permutation matrix of the cycle
`(1, 2, …, n)`, is a polytope with `(1 − ε)(D − (1/n)Iₙ) ⊆ Q ⊆ D − (1/n)Iₙ` and
`xc(Q) ≤ n · xc(P)`.

**Formalization Note.** Sets of matrices are flattened by `Matrix.vec` (`shiftedDensity`); the
congruence `X ↦ M X Mᵀ` with `M = Sⁱ U` acts on a flattened `v` through the inverse of `vec`,
`X i j = v (j, i)`, and `Sⁱ U X Uᵀ S⁻ⁱ = M X Mᵀ` since `S⁻ⁱ = (Sⁱ)ᵀ`. `S` is
`(finRotate n).permMatrix ℝ`; the sum runs over the exponents `1, …, n`. Such a `U` exists by the
spectral theorem. `Tr A = 1` forces `n ≥ 1`. -/
theorem reduction_to_identity (n : ℕ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (htr : A.trace = 1)
    (P : Set (Fin n × Fin n → ℝ)) (hP : IsPolytope P)
    (hin : (1 - ε) • shiftedDensity n A ⊆ P) (hout : P ⊆ shiftedDensity n A)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (hdiag : (U * A * Uᵀ).IsDiag) :
    let Q : Set (Fin n × Fin n → ℝ) := (n : ℝ)⁻¹ • ∑ i : Fin n,
      (fun v : Fin n × Fin n → ℝ =>
        Matrix.vec (((finRotate n).permMatrix ℝ ^ ((i : ℕ) + 1) * U) *
          Matrix.of (fun a b => v (b, a)) *
          ((finRotate n).permMatrix ℝ ^ ((i : ℕ) + 1) * U)ᵀ)) '' P
    IsPolytope Q ∧
      (1 - ε) • shiftedDensity n ((n : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) ⊆ Q ∧
      Q ⊆ shiftedDensity n ((n : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
      extensionComplexity Q ≤ n * extensionComplexity P := by sorry

end PSDPolyApprox
