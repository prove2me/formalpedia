-- Prove2me | Theorems.Thm_PoSUndirected_Supplement_theorem_4_5
-- name    : PoSUndirected.Supplement.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:35:27.248195+00:00
-- url     : https://prove2.me/theorems/5ceed48f-4940-41ec-9cb1-699dd3a1f5e2
-- title:
--   Theorem 4.5 — one additional group, exact supremum $1+1/(r+s)$
-- statement:
--   Fix integers $r,s\ge1$. Let $G$ be connected, let $F$ be a forest contained in some physical minimum spanning tree, and give every $f\in F$ at least $r$ independently labelled endpoint owners. Let the remaining players be exactly $s$ independently labelled players with one common terminal pair anywhere in $G$. For arbitrary positive real costs,
--   $$
--   \mathrm{PoS}<1+\frac1{r+s},
--   $$
--   and this is the exact class supremum for every fixed $r,s$.
--
--   With positive rational costs and multiplicities encoded in binary, a uniform polynomial-time algorithm computes an equilibrium satisfying the bound and outputs the common path once with its multiplicity rather than expanding the population.
--
--   Differences from the source:
--   - encoding: the supremum for every fixed $r,s$ → a strict upper clause over all real-cost `Fin n` presentations and an $\varepsilon$-approximation lower clause; reason: equivalent definition of the unattained class supremum, with no restriction on finite instances
--   - encoding: polynomial time with binary multiplicities and compressed path output → a Mathlib multi-tape Turing machine on binary rational instances whose output lists each owner edge with its multiplicity, followed by the common path and multiplicity $s$; reason: exact bit-complexity and the compressed representation stated by the source
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), Theorem 4.5, p.10 (PDF p.12); Appendix C, pp.56–58 (PDF pp.58–60)

import Mathlib
import Definitions.Def_PoSUndirected_Supplement_OwnerRankClassSupremum

set_option autoImplicit false

namespace PoSUndirected.Supplement

/-- **Theorem 4.5 (one additional group).** Tsoufis, preprint sha256 c095d811…, p.10
(PDF p.12); Appendix C, pp.56–58 (PDF pp.58–60).

For fixed positive integers `r,s`, an owned forest contained in a physical minimum spanning tree,
with at least `r` independent owners per forest edge and exactly `s` other players sharing one
terminal pair, has PoS strictly below `1 + 1/(r+s)` whenever ordinary PoS is defined.  This is the exact supremum for every fixed
`r,s`.  A bound-attaining equilibrium is computable in polynomial time from binary rational costs
and binary multiplicities, with every direct owner group and the common path output once together
with their multiplicities.

**Formalization Note.** The forest need not span; the common terminals are unrestricted vertices.
The player type of `AdditionalGroupInstance.game` contains no players besides the stated owner
copies and the one additional group. -/
theorem theorem_4_5 (I : AdditionalGroupRealInstance) (hI : I.Valid) :
    (∀ q : ℝ, OrdinaryPoSValue I.game I.c q →
      q < 1 + 1 / ((I.r : ℝ) + I.sN)) ∧
    AdditionalGroupClassSupremum I.r I.sN (1 + 1 / ((I.r : ℝ) + I.sN)) ∧
    HasPolynomialCompressedAdditionalGroupAlgorithm := by sorry

end PoSUndirected.Supplement
