-- Prove2me | Theorems.Thm_ShortestPlanarDisjoint_Main_lemma_4_1
-- name    : ShortestPlanarDisjoint.Main.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:38:00.28223+00:00
-- url     : https://prove2.me/theorems/5f45cc49-b4a1-4704-820c-0c424ce0592b
-- title:
--   Lemma 4.1 — Isolation with the prescribed perturbation
-- statement:
--   Let $G$ be a finite undirected simple planar graph on $n$ vertices with $k>0$
--   prescribed pairs of distinct terminals, and suppose a linkage exists. Write
--   $m=|E(G)|$, choose $R_0$ as the least power of two at least $mn$, and independently
--   choose each $R(e)$ uniformly in $\{1,\ldots,R_0\}$. For original nonnegative integer
--   costs $w$, set $\ell=(mn)^2w+R$. Then
--
--   $$\Pr_R\bigl[\text{there is a unique minimum-}\ell\text{ linkage}\bigr]
--     \ge 1-\frac1n.$$
--
--   Distinct terminals and $k>0$ imply $n\ge2$; feasibility implies $m\ge1$. Thus the
--   probability denominator and perturbation range are nonzero. The event compares
--   against all linkages, not only the original-cost minimizers. This is the isolation
--   guarantee used for the search reduction, with its exact range and scaled costs.
--
--   Differences from the source:
--   - generalization: the connected reduction and polynomially bounded original costs of Section 4 → possibly disconnected planar graphs and arbitrary nonnegative integer original costs; reason: the finite-set isolation assertion holds unchanged for these instances; the stated hypotheses include every source instance
--   - encoding: uniform independent integers in {1,…,R₀} and probability → a function from actual edges to Fin R₀, incremented by one, and the rational fraction of successful assignments; reason: this is the same uniform product law; the minimum event includes both attainment and uniqueness
--   - encoding: an arbitrary finite vertex set and unordered terminal-pair paths → vertices labelled by Fin n, unordered edges in Sym2 (Fin n), and one oriented Mathlib simple walk from the smaller terminal label in each pair; reason: every finite source instance can be relabelled bijectively; fixed path orientations remove representation duplicates without changing the linkage or its cost
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Lemma 4.1, p. 13 (PDF p. 15)

import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar
import Definitions.Def_ShortestPlanarDisjoint_Main_Isolation

set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main

/-- Lemma 4.1 with the §4 nontrivial-instance assumptions made explicit.
The perturbation is uniform over the full independent product [1,R₀]^E. -/
theorem lemma_4_1 {n k : ℕ} (I : RoutingInput n k)
    (hk : 0 < k) (hplanar : RobertsonSeymour1986.GM5.IsPlanar I.graph)
    (hfeasible : Nonempty (Linkage I)) :
    1 - 1 / (n : ℚ) ≤ isolationProbability I := by sorry

end ShortestPlanarDisjoint.Main
