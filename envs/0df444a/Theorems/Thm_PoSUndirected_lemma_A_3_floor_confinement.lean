-- Prove2me | Theorems.Thm_PoSUndirected_lemma_A_3_floor_confinement
-- name    : PoSUndirected.lemma_A_3_floor_confinement
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:00:18.113635+00:00
-- url     : https://prove2.me/theorems/9b3e353b-6040-4b71-99bf-30d966693e32
-- title:
--   Lemma A.3 — floor confinement under the smaller-height conclusions
-- statement:
--   Consider the host of any finite depth $d$ at parameters $\eta(t)$, $0\le t<1$ rational, and a weak equilibrium $A$ of its owned-edge game. Let $b$ be a block, and assume the smaller-height conclusions: every block of smaller height than $b$ has confined owners and charges each of its $r\ge1$ external users more than its ceiling cost divided by $r$. Then every immediate floor owner of $b$ is confined: for every floor unit $e$ of $b$, the owner's path lies in $D(e)$, the unit together with its child block.
--
--   Floor confinement is the first half of the height induction: the seven units of a segment make an escape from a unit cost at least $3b_0$ for a unit of cost $b_0$.
--
--   **Formalization Note** Height is $d$ minus depth, so "smaller height" means greater depth; at height one the hypothesis is vacuous. Players may use any simple path of the whole host.
--
--   Differences from the source:
--   - encoding: smaller-height blocks → every block of greater depth in the depth-$d$ host; reason: height $=d-$depth
--   - encoding: the parameters of the construction → $\eta(t)=(1-t)\eta_0+t\eta_1$ with $t$ rational and $0\le t<1$; reason: §A.5, p.18 (PDF p.20): "Throughout the construction use η(t) = (1 − t)η0 + tη1, where t is rational and 0 ≤ t < 1"
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), Lemma A.3, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_PoSUndirected_gadgetRegion

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace PoSUndirected

/-- Tsoufis (preprint, sha256 c095d811…), Lemma A.3 (Floor confinement), p.14 (PDF p.16). In the
construction at `η(t)`, `0 ≤ t < 1` rational, of any finite depth `d`: in every weak equilibrium
`A`, if every block of smaller height than the block `b` has confined owners and charges each of
its `r ≥ 1` external users more than its ceiling cost divided by `r` (the smaller-height
conclusions), then every immediate floor owner of `b` is confined: the owner of each floor unit
`e` of `b` routes inside `D(e)`.

**Formalization Note.** "Smaller height" is greater depth in the depth-`d` host (height
`= d − depth`); at height one the hypothesis is vacuous. The players may use any simple path of
the whole host (`hostGame`); confinement is a conclusion, not a restriction. -/
theorem lemma_A_3_floor_confinement (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (d : ℕ)
    (A : HEdge d → Finset (HEdge d)) (hA : IsPureNash (hostGame (etaAt t) d) A) (b : HBlock d)
    (hsmall : SmallerHeightConcl (etaAt t) A b) :
    ∀ (g : Fin 7) (σ : Fin 13) (u : Fin 7),
      A (HEdge.floor b.1 b.2 g σ u) ⊆ unitRegion b.1 b.2 g σ u := by sorry

end PoSUndirected
