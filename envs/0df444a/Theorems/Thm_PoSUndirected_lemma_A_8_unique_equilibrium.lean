-- Prove2me | Theorems.Thm_PoSUndirected_lemma_A_8_unique_equilibrium
-- name    : PoSUndirected.lemma_A_8_unique_equilibrium
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:00:41.775209+00:00
-- url     : https://prove2.me/theorems/ceea1c32-a6f0-4fc2-87f3-e86c5a60f650
-- title:
--   Lemma A.8 — the all-direct profile is the unique weak equilibrium of every finite-depth construction game
-- statement:
--   For every rational $0\le t<1$ and every depth $d\ge0$, a profile $A$ of the owned-edge game on the depth-$d$ host at $\eta(t)$ is a weak Nash equilibrium if and only if every player uses her own edge:
--   $$
--   A\ \text{is a weak equilibrium}\iff A_e=\{e\}\ \text{for every edge } e .
--   $$
--
--   This gives both existence and uniqueness; ties are allowed, so it excludes every cheaper equilibrium even under the weak convention.
--
--   Differences from the source:
--   - encoding: "the all-direct profile as its unique weak Nash equilibrium" → the equivalence above for every profile; reason: the two directions are existence and uniqueness
--   - encoding: the parameters of the construction → $\eta(t)=(1-t)\eta_0+t\eta_1$ with $t$ rational and $0\le t<1$; reason: §A.5, p.18 (PDF p.20): "Throughout the construction use η(t) = (1 − t)η0 + tη1, where t is rational and 0 ≤ t < 1"
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), Lemma A.8, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_PoSUndirected_gadgetRegion

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace PoSUndirected

/-- Tsoufis (preprint, sha256 c095d811…), Lemma A.8 (Unique weak equilibrium), p.17 (PDF p.19).
Every finite-depth game in the construction (at `η(t)`, `0 ≤ t < 1` rational) has the all-direct
profile as its unique weak Nash equilibrium: a profile is a weak equilibrium if and only if every
player uses her own edge.

**Formalization Note.** Depth `d = 0` is the roof alone. The equivalence contains both existence
(the all-direct profile is an equilibrium) and uniqueness; ties are allowed (`IsPureNash` uses
`≤`). -/
theorem lemma_A_8_unique_equilibrium (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (d : ℕ)
    (A : HEdge d → Finset (HEdge d)) :
    IsPureNash (hostGame (etaAt t) d) A ↔ A = directProfile := by sorry

end PoSUndirected
