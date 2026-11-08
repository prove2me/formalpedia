-- Prove2me | Theorems.Thm_PoSUndirected_section_A_4_opt_tree
-- name    : PoSUndirected.section_A_4_opt_tree
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:00:52.076213+00:00
-- url     : https://prove2.me/theorems/9b6608be-37f6-4eae-93bb-5e4e4484373c
-- title:
--   §A.4 — $T_d$ is the unique minimum spanning tree and $\mathrm{OPT}=O_d$
-- statement:
--   For every rational $0\le t<1$ and every depth $d\ge0$, in the host at $\eta(t)$:
--
--   1. $T_d$ is a spanning tree;
--   2. every other spanning tree has strictly larger cost: $T_d$ is the unique minimum spanning tree;
--   3. $\mathrm{OPT}=\min_P C(P)=O_d=c(T_d)$: some profile of the owned-edge game has social cost $O_d$, and every profile costs at least $O_d$.
--
--   Together with the cost identities this identifies the denominator of the price of stability of the construction.
--
--   Differences from the source:
--   - encoding: $\mathrm{OPT}=O_{d}$ → a profile attains $O_d$ and every profile costs at least $O_d$; reason: definition of the minimum over the finitely many profiles
--   - encoding: "the unique minimum spanning tree" → $T_d$ is a spanning tree and every other spanning tree costs strictly more; reason: definition of uniqueness of the minimizer
--   - encoding: the parameters of the construction → $\eta(t)=(1-t)\eta_0+t\eta_1$ with $t$ rational and $0\le t<1$; reason: §A.5, p.18 (PDF p.20): "Throughout the construction use η(t) = (1 − t)η0 + tη1, where t is rational and 0 ≤ t < 1"
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), §A.4, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_PoSUndirected_gadgetRegion

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace PoSUndirected

/-- Tsoufis (preprint, sha256 c095d811…), §A.4, p.17 (PDF p.19): "Consequently `T_drec` is the
unique minimum spanning tree and `OPT = O_drec`." In the construction at `η(t)`, `0 ≤ t < 1`
rational, of any finite depth `d`: the tree `T_d` (every expanded ceiling replaced by its seven
serial floor trees) is a spanning tree of the host, every other spanning tree costs strictly more,
and the optimum social cost over all profiles equals `O_d = c(T_d)` (attained, and a lower bound for
every profile).

**Formalization Note.** `OPT = min_P C(P)` is stated as attainment plus a lower bound. Spanning trees
are acyclic edge sets joining every two vertices (`IsSpanningTree`). -/
theorem section_A_4_opt_tree (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (d : ℕ) :
    IsSpanningTree (hostEnds d) (treeEdges d) ∧
    (∀ T : Finset (HEdge d), IsSpanningTree (hostEnds d) T → T ≠ treeEdges d →
      Od (etaAt t) d < ∑ e ∈ T, hostCost (etaAt t) e) ∧
    (∃ P, IsProfile (hostGame (etaAt t) d) P ∧
      designCost (fun e _ => (hostCost (etaAt t) e : ℝ)) P = (Od (etaAt t) d : ℝ)) ∧
    (∀ P, IsProfile (hostGame (etaAt t) d) P →
      (Od (etaAt t) d : ℝ) ≤ designCost (fun e _ => (hostCost (etaAt t) e : ℝ)) P) := by sorry

end PoSUndirected
