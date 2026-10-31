-- Prove2me | Theorems.Thm_ParriloTheta_clique_partition_certificate
-- name    : ParriloTheta.clique_partition_certificate
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:31:42.062644+00:00
-- url     : https://prove2.me/theorems/aa46a0c4-6fcb-4c88-b176-61b93e5ff367
-- title:
--   p.12 — a partition into $\alpha(G)$ cliques gives a $\mathcal K^{(0)}$-certificate and $\vartheta$-rank $0$
-- statement:
--   Let $G=(V,E)$ be a graph with $\alpha(G)=\alpha$, and let $V=V_1\cup\dots\cup V_\alpha$ be a partition of $V$ into cliques. Let $P$ be the matrix with $P_{uv}=\alpha-1$ if $u,v$ lie in the same part and $P_{uv}=-1$ otherwise, i.e. in block form
--   $$
--   P=\begin{pmatrix}(\alpha-1)J&-J&\cdots&-J\\-J&(\alpha-1)J&\cdots&-J\\ \vdots&&\ddots&\vdots\\-J&-J&\cdots&(\alpha-1)J\end{pmatrix}.
--   $$
--   Then $P$ is a $\mathcal K^{(0)}$-certificate for $M_G$, and $\vartheta\text{-rank}(G)=0$.
--
--   In particular a graph covered by $\alpha(G)$ cliques has $\vartheta$-rank $0$; the paper uses this for the graphs $C_{2n+1}\setminus i^\perp$ and $\overline{C_{2n+1}}\setminus i^\perp$.
--
--   **Formalization Note** The partition is a labelling $f:V\to\{0,\dots,\alpha-1\}$ whose label classes are cliques (some classes may be empty; a cover by $\alpha$ cliques always refines to such a labelling).
--
--   Differences from the source:
--   - encoding: a graph G = (V, E) with V = [n] → G : SimpleGraph V on a finite type V; α(G) = G.indepNum; reason: Lean convention; the same graphs up to relabelling
--   - encoding: ϑ-rank(G) ∈ ℕ ∪ {∞} → thetaRank G : ℕ∞ (⊤ = ∞); reason: Lean convention; same values
--   - encoding: cliques V_1, …, V_α partitioning V → f : V → Fin α(G) with every label class a clique; reason: same partitions (parts may be empty, as a cover by α cliques can produce)
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, p.12 (paragraph after (5.1))

import Mathlib
import Definitions.Def_ParriloTheta_graphMatrix
import Definitions.Def_ParriloTheta_IsK0Cert
import Definitions.Def_ParriloTheta_thetaRank

namespace ParriloTheta

/-- **A partition into `α(G)` cliques gives a `K^(0)`-certificate, and ϑ-rank 0.**
Laurent & Vargas, *Exactness of Parrilo's conic approximations for copositive matrices and
associated low order bounds for the stability number of a graph*, arXiv:2109.12876v1, p.12: "if G can be covered by α(G) cliques then G has ϑ-rank 0. In addition, if
α(G) = α and V1, V2, . . . , Vα are cliques partitioning V then the matrix P := ((α−1)J, −J, …;
−J, (α−1)J, …; …), whose block-structure is induced by the partition V = V1 ∪ · · · ∪ Vα, is a
K(0)-certificate for MG."

The partition is given by `f : V → Fin α(G)` whose fibres are cliques; `P_uv = α − 1` if `u`
and `v` lie in the same part and `−1` otherwise.

**Formalization Note.** A cover by `α(G)` cliques can always be refined to a partition into
`α(G)` (possibly empty) cliques, which is what `f` encodes, so both claims of the page are
covered. -/
theorem clique_partition_certificate {V : Type*} [Fintype V] (G : SimpleGraph V)
    (f : V → Fin G.indepNum) (hf : ∀ u v, u ≠ v → f u = f v → G.Adj u v) :
    IsK0Cert (graphMatrix G)
        (Matrix.of fun u v => if f u = f v then (G.indepNum : ℝ) - 1 else -1) ∧
      thetaRank G = 0 := by sorry

end ParriloTheta
