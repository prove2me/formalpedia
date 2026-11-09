-- Prove2me | Theorems.Thm_WeightedThreeSetPacking_Main_lemma_3_2
-- name    : WeightedThreeSetPacking.Main.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:19.415377+00:00
-- url     : https://prove2.me/theorems/fe6b509d-5f86-4d7d-991d-ddac080db382
-- title:
--   Lemma 3.2 — Final-root tree slack (Tong and Xu, arXiv:2610.10036v1, p. 9)
-- statement:
--   Under the standing setting of Tong and Xu, arXiv:2610.10036v1, Lemma 3.2, p. 9, use the inclusive neighborhoods, claws and exact parameters defined above.
--
--   $$\sum_{v\in T}(\Delta_v/w_v+\Psi_v/w_v)\ge Q(T)+(\rho_3(\epsilon_2)-3\epsilon_2)w(T)+(1-\epsilon_2)\sum_{(u,v)\in E(H[T])}w_u.$$ The subtree inequalities remain explicit assumptions, alongside the standing bounded square local optimality of Phase I. Thresholds and the size parameter are generic, rather than fixed to Section 4 constants.
--
--   This result provides the corresponding source statement in the dependency chain for the full approximation theorem.
--
--   Differences from the source:
--   - generalization: Positive rational set weights, an optimum packing O, and its rank-three conflict graph (or an analysis lift). → Positive real weights on A∪O, independent O, and finite graphs with the inherited two-sided inclusive degree bounds and maximum-neighbor assignment.; reason: These inequalities use positivity, independence and the rank-three degree bounds; every source instance and its weight-preserving lift satisfies these assumptions.
--   - encoding: Finite set families, inclusive neighborhoods, witnessed exchange multiarcs and finite sums. → Finite carrier types and Finsets, with one triple per witnessed arc and inclusive neighborhoods.; reason: This preserves common vertices, distinct-neighbor sums and incidence multiplicities.
--   - generalization: A final piece after the Arkin–Hassin reduction with the larger fixed girth required for the full decomposition. → A computed final component with graph girth greater than twice its maximum possible vertex count.; reason: A cycle or parallel-arc obstruction in a final piece would give a conflict cycle of length at most twice that count; no full root/pendant hierarchy is needed for these final pieces.
--   - encoding: The standing Phase I square local optimality and the explicit connected-subtree hypothesis, with generic layer size ℓ. → SquareLocal at (9ℓ)³ times the sum of (3ℓ)^(2r) for 0≤r≤2ℓ−2, plus the explicit subtree hypothesis; ℓ is the cutoff field.; reason: The exchange radius is the k=3,L=3 formula on p. 10 and Appendix A, p. 32; ℓ=7 recovers s₀ exactly. The inherited condition is not a new approximation certificate.
--   - encoding: The exchange-layer framework has thresholds satisfying 1−εᵢ=(1−εᵢ₋₁)² (Appendix A.3, pp. 30–31; Section 4, p. 10). → LayerParameters explicitly requires the recurrence for all three transitions, along with its positivity and cutoff conditions.; reason: This is an inherited source assumption, not an additional restriction on its layer framework; ordered thresholds alone would state a different, false generalization.
-- source:
--   Tong and Xu, arXiv:2610.10036v1, Lemma 3.2, p. 9; https://arxiv.org/abs/2610.10036v1

import Definitions.Def_WeightedThreeSetPacking_Main_Analysis

namespace WeightedThreeSetPacking.Main

open scoped BigOperators

/-- Tong and Xu, arXiv:2610.10036v1, Lemma 3.2, p. 9. -/
theorem lemma_3_2 {V : Type} [Fintype V] [DecidableEq V] (D : Analysis V)
    (hvalid : ValidAnalysis D)
    (hparameters : LayerParameters D) (hgirth : FinalHighGirth D)
    (hlocal : SquareLocal D (layerExchangeRadius D.cutoff))
    (T : Finset V) (hfinal : FinalComponent D T)
    (hsubtrees : ∀ R, ConnectedSubtree D T R →
      squareMass D (jointClaw D R) ≤ squareMass D (jointNeighborhood D R)) :
    slackSum D T ≥ layerCredit D T +
      (rho (1 - D.threshold 2) - 3 * (1 - D.threshold 2)) * mass D T +
      D.threshold 2 * ∑ e ∈ internalArcs D T 4, D.w e.2.1 := by sorry

end WeightedThreeSetPacking.Main
