-- Prove2me | Theorems.Thm_SpectralSparsify_Decomp_lemma_7_2
-- name    : SpectralSparsify.Decomp.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:36:26.307451+00:00
-- url     : https://prove2.me/theorems/598a2b88-5474-4599-80bd-46e37661949d
-- title:
--   Lemma 7.2 (Sparsest Cuts as Certificates) — if the largest sparse cut S has Vol(S) = αVol(B), α ≤ 1/3, then Φ^G_{B−S} ≥ φ(1−3α)/(1−α)
-- statement:
--   Let $G=(V,E)$ be a finite simple graph without isolated vertices, with volumes and conductances $\Phi^G_B$ measured by the degrees of $G$, and let $\varphi\le 1$. Let $B\subseteq V$ be nonempty and let $S\subset B$ be a proper subset of $B$ maximizing $\operatorname{Vol}(S)$ among the proper subsets of $B$ satisfying
--
--   1. (C.1) $\operatorname{Vol}(S)\le\operatorname{Vol}(B)/2$, and
--   2. (C.2) $\Phi^G_B(S)\le\varphi$.
--
--   If $\operatorname{Vol}(S)=\alpha\operatorname{Vol}(B)$ for $\alpha\le 1/3$, then
--   $$\Phi^G_{B-S}\ \ge\ \varphi\left(\frac{1-3\alpha}{1-\alpha}\right).$$
--
--   The lemma says that if the largest set of conductance at most $\varphi$ is small, then the rest of $B$ has conductance almost $\varphi$; it certifies the conductance of the parts the decomposition procedure of Theorem 7.1 returns.
--
--   **Formalization Note** The paper leaves implicit that $G$ has no isolated vertices (otherwise $\Phi^G_B(S)$ is $0/0$ for sets of isolated vertices, and with Lean's convention $0/0=0$ the statement fails), and that $B$ is nonempty (so that $\alpha=\operatorname{Vol}(S)/\operatorname{Vol}(B)$ is determined and lies in $[0,1/2]$); both are hypotheses. The maximality of $S$ is the hypothesis that every proper subset $S'\subset B$ satisfying (C.1) and (C.2) has $\operatorname{Vol}(S')\le\operatorname{Vol}(S)$. The number $\alpha$ is a real variable tied to $S$ by $\operatorname{Vol}(S)=\alpha\operatorname{Vol}(B)$, as printed.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 18, Lemma 7.2

import Mathlib
import Definitions.Def_SpectralSparsify_Decomp_vol
import Definitions.Def_SpectralSparsify_Decomp_cutEdges
import Definitions.Def_SpectralSparsify_Decomp_cond

namespace SpectralSparsify.Decomp

/-- Lemma 7.2 (Sparsest Cuts as Certificates), arXiv:0808.4134v3, p. 18. Let `G` be a graph
without isolated vertices and `φ ≤ 1`. Let `B` be a nonempty vertex set and `S ⊂ B` a set
maximizing `Vol(S)` among the proper subsets of `B` satisfying (C.1) `Vol(S) ≤ Vol(B)/2` and
(C.2) `Φ^G_B(S) ≤ φ`. If `Vol(S) = α Vol(B)` with `α ≤ 1/3`, then
`Φ^G_{B - S} ≥ φ (1 - 3α)/(1 - α)`. -/
theorem lemma_7_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ v, 0 < G.degree v) (φ : ℝ) (hφ : φ ≤ 1)
    (B S : Finset V) (hB : B.Nonempty) (hSB : S ⊂ B)
    (hC1 : vol G S ≤ vol G B / 2) (hC2 : condRel G B S ≤ φ)
    (hmax : ∀ S' : Finset V, S' ⊂ B → vol G S' ≤ vol G B / 2 → condRel G B S' ≤ φ →
      vol G S' ≤ vol G S)
    (α : ℝ) (hα : vol G S = α * vol G B) (hα3 : α ≤ 1 / 3) :
    φ * ((1 - 3 * α) / (1 - α)) ≤ cond G (B \ S) := by sorry

end SpectralSparsify.Decomp
