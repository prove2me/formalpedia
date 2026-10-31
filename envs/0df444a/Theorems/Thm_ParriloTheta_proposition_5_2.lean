-- Prove2me | Theorems.Thm_ParriloTheta_proposition_5_2
-- name    : ParriloTheta.proposition_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:31:21.407222+00:00
-- url     : https://prove2.me/theorems/a618746c-1f66-482a-9ee1-288d6faa5321
-- title:
--   Proposition 5.2 — if $\vartheta\text{-rank}(G)=0$, every component of $G_c$ is a clique of $G$
-- statement:
--   Let $G=(V,E)$ be a graph, let $E_c$ be its set of critical edges (edges $e$ with $\alpha(G\setminus e)=\alpha(G)+1$) and $G_c=(V,E_c)$. If $\vartheta\text{-rank}(G)=0$, then each connected component of $G_c$ is a clique of $G$: any two distinct nodes joined by a path of critical edges are adjacent in $G$.
--
--   This is the structural obstruction to $\vartheta$-rank $0$ used to show that odd cycles and their complements have $\vartheta$-rank exactly $1$.
--
--   Differences from the source:
--   - encoding: a graph G = (V, E) with V = [n] → G : SimpleGraph V on a finite type V; α(G) = G.indepNum; reason: Lean convention; the same graphs up to relabelling
--   - encoding: ϑ-rank(G) ∈ ℕ ∪ {∞} → thetaRank G : ℕ∞ (⊤ = ∞); reason: Lean convention; same values
--   - encoding: each connected component of G_c is a clique of G → ∀ u v, G_c.Reachable u v → u = v ∨ G.Adj u v; reason: the same property
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, Proposition 5.2, p.12

import Mathlib
import Definitions.Def_ChvatalPolytopes_Separation_AlphaCritical
import Definitions.Def_ParriloTheta_thetaRank

namespace ParriloTheta

open ChvatalPolytopes.Separation

/-- **Proposition 5.2: under ϑ-rank 0, components of `G_c` are cliques.**
Laurent & Vargas, *Exactness of Parrilo's conic approximations for copositive matrices and
associated low order bounds for the stability number of a graph*, arXiv:2109.12876v1, Proposition 5.2, p.12:
"Let G = (V, E) be a graph, let Ec denote the set of critical edges of G and let Gc = (V, Ec) be
the corresponding subgraph of G. If ϑ-rank(G) = 0 then each connected component of the graph Gc is
a clique of G."

**Formalization Note.** `G_c` is the published `criticalGraph G` (an edge `e` is critical when
`α(G \ e) = α(G) + 1`, p.4). "Each connected component of `G_c` is a clique of `G`": any two
distinct nodes joined by a path in `G_c` are adjacent in `G`. -/
theorem proposition_5_2 {V : Type*} [Finite V] (G : SimpleGraph V) (h : thetaRank G = 0) :
    ∀ u v : V, (criticalGraph G).Reachable u v → u = v ∨ G.Adj u v := by sorry

end ParriloTheta
