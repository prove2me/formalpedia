-- Prove2me | Theorems.Thm_PSDPolyApprox_xc_minkowski_sum
-- name    : PSDPolyApprox.xc_minkowski_sum
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:49:23.993795+00:00
-- url     : https://prove2.me/theorems/3e58b322-0326-4e0e-bf80-7e13f9e6e0a0
-- title:
--   §3, p.4 — the extension complexity of a Minkowski sum is at most the sum: $\operatorname{xc}(P_1+P_2)\le\operatorname{xc}(P_1)+\operatorname{xc}(P_2)$
-- statement:
--   For polytopes $P_1,P_2\subseteq\mathbb R^d$, the extension complexity of their Minkowski sum $P_1+P_2=\{p_1+p_2: p_1\in P_1,\ p_2\in P_2\}$ is at most the sum of their extension complexities:
--   $$
--   \operatorname{xc}(P_1+P_2)\le\operatorname{xc}(P_1)+\operatorname{xc}(P_2).
--   $$
--   It is used, through the Minkowski average of $n$ rotated copies of $P$, to reduce Theorem 1 to the case $A=\frac1nI_n$.
--
--   Differences from the source:
--   - encoding: extension complexity = smallest number of facets of a polytope whose linear image is P (Definition 1) → smallest number of inequalities of an extended formulation of P (ExtensionComplexity.TSP.extensionComplexity); reason: the two minima coincide for polytopes of dimension ≥ 1 (Fiorini et al., J. ACM 2015, Theorem 3, published as ExtensionComplexity.TSP.yannakakis_factorization); for a point or the empty set the inequality count is 0 and never exceeds the facet count, so in those degenerate cases the Lean inequality still implies the paper's
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, §3, p.4 ("It is known and easy to verify …")

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_Polytope
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity

open ExtensionComplexity.TSP
open scoped Pointwise

namespace PSDPolyApprox

/-- **Extension complexity of a Minkowski sum.**
Fawzi, arXiv:1811.09649v1, §3, p.4: "It is known and easy to verify that the extension
complexity of the Minkowski sum of two polytopes is at most the sum of the extension
complexities."

For polytopes `P₁, P₂ ⊆ ℝ^ι`: `xc(P₁ + P₂) ≤ xc(P₁) + xc(P₂)`.

**Formalization Note.** `P₁ + P₂` is the pointwise (Minkowski) sum of sets; `xc` is the
minimum size of an extended formulation (`ExtensionComplexity.TSP.extensionComplexity`). -/
theorem xc_minkowski_sum {ι : Type*} [Fintype ι] (P₁ P₂ : Set (ι → ℝ))
    (h₁ : IsPolytope P₁) (h₂ : IsPolytope P₂) :
    extensionComplexity (P₁ + P₂) ≤ extensionComplexity P₁ + extensionComplexity P₂ := by sorry

end PSDPolyApprox
