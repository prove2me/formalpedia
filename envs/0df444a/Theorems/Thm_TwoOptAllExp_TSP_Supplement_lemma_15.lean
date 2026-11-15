-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_Supplement_lemma_15
-- name    : TwoOptAllExp.TSP.Supplement.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:46:10.767065+00:00
-- url     : https://prove2.me/theorems/99339f0c-a9cc-4901-9433-841accab8baa
-- title:
--   Lemma 15 — a weighted graph objective of maximum degree $\le q$ is a $(2,q,2)$-MCA objective
-- statement:
--   Let $q\ge1$ and let $G=(V,E)$ be a finite simple graph of maximum degree at most $q$, with edge weights $w:E\to\mathbb Z$ and vertex weights $b:V\to\mathbb Z$. Then there is a $(2,q,2)$-MCA instance whose variables are identified with the vertices of $G$ (by a bijection $e$) and whose value function equals the graph objective:
--
--   $$\Phi_I(\sigma\circ e^{-1})=\sum_{uv\in E}w(uv)[\sigma(u)\ne\sigma(v)]+\sum_{v\in V}b_v\sigma(v)\qquad\text{for every }\sigma:V\to\{0,1\}.$$
--
--   It lets the Section 5 construction be specified by vertex and edge weights alone.
--
--   Differences from the source:
--   - encoding: the objective defines a (2,q,2)-MCA instance with the same objective function → ∃ instance I and a bijection e : V ≃ Fin I.N with I.IsPQ 2 q and I.Φ (σ ∘ e.symm) = Φ σ for all σ; reason: the MCA instance has its own variable indices; e identifies them with the vertices
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Lemma 15, p. 25

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Supplement_GraphObjective

namespace TwoOptAllExp.TSP.Supplement

/-- **Lemma 15** (p. 25). Let `q ≥ 1`. If `G` has maximum degree at most `q`, then any objective
`Φ(σ) = ∑_{uv ∈ E} w(uv)[σ(u) ≠ σ(v)] + ∑_v b_v σ(v)` defines a `(2, q, 2)`-MCA instance with the
same objective function (its variables identified with the vertices by `e`). -/
theorem lemma_15 {V : Type} [Fintype V] [DecidableEq V] (q : ℕ) (hq : 1 ≤ q) (W : WGraph V)
    (hdeg : ∀ x : V, W.G.degree x ≤ q) :
    ∃ (I : MCAInstance) (e : V ≃ Fin I.N), I.IsPQ 2 q ∧
      ∀ σ : V → Bool, I.Φ (σ ∘ e.symm) = W.Φ σ := by sorry

end TwoOptAllExp.TSP.Supplement
