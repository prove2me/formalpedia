-- Prove2me | Theorems.Thm_SpectralSparsify_Decomp_theorem_7_1
-- name    : SpectralSparsify.Decomp.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:35:29.869233+00:00
-- url     : https://prove2.me/theorems/706a3e79-13c9-45b7-9a00-55bab4d938da
-- title:
--   Theorem 7.1 — every graph with m edges has a (6 log_{4/3} 2m)⁻¹-decomposition with |∂(A₁, …, A_k)| ≤ |E|/2
-- statement:
--   Let $G=(V,E)$ be a finite simple graph without isolated vertices and let $m=|E|$. Then $G$ has a decomposition $(A_1,\dots,A_k)$, that is, a partition of $V$ into nonempty sets, such that
--
--   1. every part has conductance
--   $$\Phi^G_{A_i}\ \ge\ \big(6\log_{4/3}2m\big)^{-1}\qquad(i=1,\dots,k),$$
--   where $\Phi^G_{A_i}$ measures volumes with the degrees of $G$; and
--   2. the number of edges between different parts satisfies
--   $$|\partial(A_1,\dots,A_k)|\ \le\ \frac{|E|}{2}.$$
--
--   Both conditions hold for the same partition: a partition into singletons has conductance $1$ everywhere but cuts every edge, and the trivial partition cuts nothing but may have small conductance. The theorem is the existence statement behind the paper's spectral sparsifiers: each high-conductance part can be sparsified by sampling, and the at most $|E|/2$ crossing edges are handled recursively.
--
--   **Formalization Note** The paper leaves implicit that $G$ has no isolated vertices; conductance is $0/0$ otherwise, and the hypothesis is the setting in which $\Phi^G_B$ is defined. Under it, $m=0$ forces $V=\emptyset$ and the statement is trivially true (Lean's $\log_{4/3}0=0$ makes the bound $0^{-1}=0$). The logarithm is `Real.logb (4/3)` applied to $2m=\operatorname{Vol}(V)$. The bound on the boundary is stated over $\mathbb R$ as $|\partial|\le m/2$.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 17, Theorem 7.1 (proof p. 19)

import Mathlib
import Definitions.Def_SpectralSparsify_Decomp_cond
import Definitions.Def_SpectralSparsify_Decomp_decompBoundary

namespace SpectralSparsify.Decomp

/-- Theorem 7.1 (arXiv:0808.4134v3, p. 17). Let `G = (V, E)` be a graph without isolated
vertices and `m = |E|`. Then `G` has a `(6 log_{4/3} 2m)⁻¹`-decomposition `(A₁, …, A_k)`,
i.e. a partition of `V` with `Φ^G_{Aᵢ} ≥ (6 log_{4/3} 2m)⁻¹` for all `i`, whose boundary
satisfies `|∂(A₁, …, A_k)| ≤ |E|/2`. -/
theorem theorem_7_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ v, 0 < G.degree v) :
    ∃ P : Finpartition (Finset.univ : Finset V),
      (∀ A ∈ P.parts,
        (6 * Real.logb (4 / 3) (2 * (G.edgeFinset.card : ℝ)))⁻¹ ≤ cond G A) ∧
      ((decompBoundary G P).card : ℝ) ≤ (G.edgeFinset.card : ℝ) / 2 := by sorry

end SpectralSparsify.Decomp
