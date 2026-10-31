-- Prove2me | Theorems.Thm_ParriloTheta_lemma_4_7
-- name    : ParriloTheta.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:31:10.637406+00:00
-- url     : https://prove2.me/theorems/8c3add0e-8645-4cea-8849-c21a754c620f
-- title:
--   Lemma 4.7 (de Klerk–Pasechnik) — $\vartheta\text{-rank}(G\setminus i^\perp)=0$ for all $i$ implies $\vartheta\text{-rank}(G)\le1$
-- statement:
--   Let $G=(V,E)$ be a graph. If $\vartheta\text{-rank}(G\setminus i^\perp)=0$ for every node $i\in V$, then
--   $$
--   \vartheta\text{-rank}(G)\le1 .
--   $$
--   Here $G\setminus i^\perp$ is the subgraph induced by the nodes that are neither $i$ nor adjacent to $i$.
--
--   Differences from the source:
--   - encoding: a graph G = (V, E) with V = [n] → G : SimpleGraph V on a finite type V; α(G) = G.indepNum; reason: Lean convention; the same graphs up to relabelling
--   - encoding: ϑ-rank(G) ∈ ℕ ∪ {∞} → thetaRank G : ℕ∞ (⊤ = ∞); reason: Lean convention; same values
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, Lemma 4.7, p.11

import Mathlib
import Definitions.Def_ParriloTheta_thetaRank
import Definitions.Def_ParriloTheta_delNbhd

namespace ParriloTheta

/-- **Lemma 4.7 (de Klerk and Pasechnik [5]).**
Laurent & Vargas, *Exactness of Parrilo's conic approximations for copositive matrices and
associated low order bounds for the stability number of a graph*, arXiv:2109.12876v1, Lemma 4.7, p.11: "If ϑ-rank(G \ i⊥) = 0 for all i ∈ V then ϑ-rank(G) ≤ 1."

**Formalization Note.** `G \ i⊥` is `delNbhd G i`, the subgraph induced by
`V ∖ ({i} ∪ N(i))`. ϑ-rank is `ℕ∞`-valued. -/
theorem lemma_4_7 {V : Type*} [Finite V] (G : SimpleGraph V)
    (h : ∀ i : V, thetaRank (delNbhd G i) = 0) :
    thetaRank G ≤ 1 := by sorry

end ParriloTheta
