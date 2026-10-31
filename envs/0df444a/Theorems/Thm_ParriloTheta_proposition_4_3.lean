-- Prove2me | Theorems.Thm_ParriloTheta_proposition_4_3
-- name    : ParriloTheta.proposition_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:30:38.5084+00:00
-- url     : https://prove2.me/theorems/f54de686-91b7-4675-8133-11ab8309289d
-- title:
--   Proposition 4.3 (Gvozdenović–Laurent) — $\vartheta\text{-rank}(G)\le1+\max_i\vartheta\text{-rank}((G\setminus i^\perp)\oplus i)$
-- statement:
--   For every graph $G=(V,E)$,
--   $$
--   \vartheta\text{-rank}(G)\le 1+\max_{i\in V}\ \vartheta\text{-rank}\big((G\setminus i^\perp)\oplus i\big),
--   $$
--   where $(G\setminus i^\perp)\oplus i$ deletes the closed neighbourhood of $i$ and adds $i$ back as an isolated node.
--
--   The paper cites this bound; it is the source of the upper bound $\vartheta$-rank $\le1$ for odd cycles and their complements (Lemma 4.7).
--
--   **Formalization Note** Computed in `ℕ∞`; for the graph with no vertices the maximum is $0$.
--
--   Differences from the source:
--   - encoding: a graph G = (V, E) with V = [n] → G : SimpleGraph V on a finite type V; α(G) = G.indepNum; reason: Lean convention; the same graphs up to relabelling
--   - encoding: ϑ-rank(G) ∈ ℕ ∪ {∞} → thetaRank G : ℕ∞ (⊤ = ∞); reason: Lean convention; same values
--   - encoding: (G ∖ i⊥) ⊕ i, with a new isolated node → the induced subgraph of G on {i} ∪ (V ∖ i⊥); reason: the same graph: i has no neighbour there
--   - encoding: max_{i∈V} → ⨆ i : V in ℕ∞; reason: the maximum of finitely many values; 0 for empty V, where the page's max is undefined
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, Proposition 4.3, eq. (4.1), p.10 (cited from Gvozdenović and Laurent [12])

import Mathlib
import Definitions.Def_ParriloTheta_thetaRank
import Definitions.Def_ParriloTheta_delNbhdAddNode

namespace ParriloTheta

/-- **Proposition 4.3 (Gvozdenović and Laurent [12]).**
Laurent & Vargas, *Exactness of Parrilo's conic approximations for copositive matrices and
associated low order bounds for the stability number of a graph*, arXiv:2109.12876v1, Proposition 4.3, eq. (4.1), p.10:
"For any graph G = (V, E) we have: ϑ-rank(G) ≤ 1 + max_{i∈V} ϑ-rank((G \ i⊥) ⊕ i)."

**Formalization Note.** In `ℕ∞`; the maximum over `V` is `⨆ i : V` (equal to `0` when `V` is
empty). `(G \ i⊥) ⊕ i` is `delNbhdAddNode G i`, the subgraph induced by `{i} ∪ (V ∖ i⊥)`. -/
theorem proposition_4_3 {V : Type*} [Finite V] (G : SimpleGraph V) :
    thetaRank G ≤ 1 + ⨆ i : V, thetaRank (delNbhdAddNode G i) := by sorry

end ParriloTheta
