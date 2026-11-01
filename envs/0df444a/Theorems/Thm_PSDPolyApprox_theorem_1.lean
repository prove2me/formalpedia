-- Prove2me | Theorems.Thm_PSDPolyApprox_theorem_1
-- name    : PSDPolyApprox.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:50:47.419983+00:00
-- url     : https://prove2.me/theorems/24f966cc-5006-419f-971b-174cf794b20b
-- title:
--   Theorem 1 (corrected: $n\ge2$) — every polytope between $(1-\epsilon)(\mathcal D-A)$ and $\mathcal D-A$ has extension complexity $\ge e^{c\sqrt n}$
-- statement:
--   **Theorem 1.** For every $0<\epsilon<1$ there is a constant $c>0$ such that the following holds. Let $n\ge2$, let $A$ be an $n\times n$ real symmetric matrix with $\operatorname{Tr}A=1$, and let $\mathcal D=\{X\in S^n_+:\operatorname{Tr}X=1\}$ be the set of density matrices. If $P$ is a polytope with
--   $$
--   (1-\epsilon)(\mathcal D-A)\subseteq P\subseteq\mathcal D-A,
--   $$
--   then the extension complexity of $P$ is at least
--   $$
--   \operatorname{xc}(P)\ge e^{c\sqrt n}.
--   $$
--   So the set of density matrices, unlike the Euclidean ball, cannot be approximated within a constant factor by a polytope that is the projection of a polytope with subexponentially many facets: every linear-programming formulation of such an approximation has size $e^{\Omega(\sqrt n)}$.
--
--   **Formalization Note** The constant $c$ depends only on $\epsilon$ and is chosen before $n$, $A$ and $P$. $A$ need not be positive semidefinite.
--
--   Differences from the source:
--   - correction: every n → n ≥ 2; reason: at n = 1, 𝒟 = {(1)} and A = (1), so 𝒟 − A = {0}, P = {0} and xc(P) = 0 < e^{c} for every c > 0
--   - encoding: sets of n × n matrices → their images in ℝ^{n×n} under the flattening Matrix.vec; reason: vec is a linear isomorphism carrying the trace inner product to the dot product; extension complexity is invariant under it (equations are free)
--   - encoding: extension complexity = smallest number of facets of a polytope whose linear image is P (Definition 1) → smallest number of inequalities of an extended formulation of P (ExtensionComplexity.TSP.extensionComplexity); reason: the two minima coincide for polytopes of dimension ≥ 1 (Fiorini et al., J. ACM 2015, Theorem 3, published as ExtensionComplexity.TSP.yannakakis_factorization), and every polytope in this statement has dimension ≥ 1
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, Theorem 1, p.2 (proof: §3, pp.4–7)

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_Polytope
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_PSDPolyApprox_shiftedDensity

open ExtensionComplexity.TSP
open scoped Pointwise

namespace PSDPolyApprox

/-- **Theorem 1.**
Fawzi, arXiv:1811.09649v1, Theorem 1, p.2: "For any 0 < ǫ < 1, there exists a constant c > 0 such
that the following is true. Let A be an n × n real symmetric matrix of trace equal to one. If P is
a polytope such that (1 − ǫ)(D − A) ⊂ P ⊂ D − A then the extension complexity of P is at least
e^{c√n}."

For every `0 < ε < 1` there is `c > 0` such that for every `n ≥ 2`, every real symmetric
`n × n` matrix `A` with `Tr A = 1` and every polytope `P` with `(1 − ε)(D − A) ⊆ P ⊆ D − A`:
`xc(P) ≥ e^{c√n}`.

**Formalization Note.** `c` depends on `ε` only and is chosen before `n`, `A`, `P`. Matrices are
flattened by `Matrix.vec` into `ℝ^{Fin n × Fin n}` (`shiftedDensity`); extension complexity is
invariant under this linear embedding (equations are free). `xc` is the minimum number of
inequalities of an extended formulation, equal to Definition 1's facet count for polytopes of
dimension `≥ 1` (Fiorini et al., Theorem 3), which `P` has for `n ≥ 2`.
**Correction** `n ≥ 2`: at `n = 1`, `D − A = {0}`, so `P = {0}` and `xc(P) = 0 < e^{c}`. -/
theorem theorem_1 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → ∀ A : Matrix (Fin n) (Fin n) ℝ, A.IsSymm → A.trace = 1 →
      ∀ P : Set (Fin n × Fin n → ℝ), IsPolytope P →
        (1 - ε) • shiftedDensity n A ⊆ P → P ⊆ shiftedDensity n A →
        Real.exp (c * Real.sqrt n) ≤ (extensionComplexity P : ℝ) := by sorry

end PSDPolyApprox
