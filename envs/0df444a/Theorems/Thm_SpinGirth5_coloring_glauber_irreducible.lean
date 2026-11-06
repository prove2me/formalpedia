-- Prove2me | Theorems.Thm_SpinGirth5_coloring_glauber_irreducible
-- name    : SpinGirth5.coloring_glauber_irreducible
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:10:32.39989+00:00
-- url     : https://prove2.me/theorems/5dfe5cff-7c95-413d-ad09-51aecd295425
-- title:
--   §6 / [Jer95] — Glauber dynamics on proper $q$-colourings is irreducible when $q\ge\Delta+2$
-- statement:
--   Let $G$ be a finite graph with maximum degree $\Delta$ and let $q\ge\Delta+2$. Then $G$ has a proper $q$-colouring, and the heat-bath Glauber dynamics on the set of proper $q$-colourings (choose a uniform vertex and recolour it uniformly from the colours absent from its neighbourhood) is irreducible: any proper colouring can reach any other with positive probability.
--
--   The paper cites this fact ([Jer95, Section 2]) to obtain irreducibility in Theorem 3 at $\beta=0$, and hence in Theorem 1.
--
--   Differences from the source:
--   - generalization: in this range (girth ≥ 5, Δ large in terms of δ, q ≥ Δ + 2) → every finite graph and every q ≥ Δ + 2; reason: the cited fact [Jer95, Section 2] holds for all graphs; the paper's range is a special case
--   - generalization: the proper-coloring Glauber dynamics is irreducible → the set of proper colourings is nonempty and the chain is irreducible; reason: nonemptiness is implicit in 'ergodic when q ≥ Δ + 2' (p.3) and holds for q ≥ Δ + 1 by greedy colouring
-- source:
--   Chen, Liu, A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least Five, arXiv:2608.25491, §6, proof of Theorem 3, p.34; §1, p.3 ([Jer95, Section 2])

import Mathlib
import Definitions.Def_mm_transport

namespace SpinGirth5

/-- **Irreducibility of the proper-colouring Glauber dynamics for `q ≥ Δ + 2`** ([Jer95, Section 2],
used in §6). For every finite graph `G` with maximum degree `Δ` and every `q ≥ Δ + 2`, the set of
proper `q`-colourings is nonempty and the heat-bath Glauber dynamics on it is irreducible.

Chen, Liu, *A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least
Five*, arXiv:2608.25491, §6, proof of Theorem 3, p.34 ("When β = 0, the assumption on q gives
q ≥ ∆ + 2 for sufficiently large ∆ in terms of δ, and the proper-coloring Glauber dynamics is
irreducible in this range [Jer95, Section 2]"); also §1, p.3 ("ergodic when q ≥ ∆ + 2").

**Formalization Note** The chain is the published `MarkovMixing.coloringGlauber G q`, the
Glauber dynamics of the uniform law on proper colourings restricted to proper colourings;
`MarkovMixing.Irreducible` asks `P^t(x, y) > 0` for some `t` for every pair of states. The paper
cites this fact; it is stated for every finite graph, without the girth assumption. -/
theorem coloring_glauber_irreducible {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) (hq : G.maxDegree + 2 ≤ q) :
    Nonempty {c : V → Fin q // MarkovMixing.IsProperColoring G c} ∧
      MarkovMixing.Irreducible (MarkovMixing.coloringGlauber G q) := by sorry

end SpinGirth5
