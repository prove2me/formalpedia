-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_lemma_1
-- name    : RandomSizeStable.Stability.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:54:00.83079+00:00
-- url     : https://prove2.me/theorems/14d77c69-ded1-44bd-a83d-f5c538e03346
-- title:
--   Lemma 1 — labeled comparison formulas, continuity and convexity
-- statement:
--   Let $D$ be an arbitrary positive-integer draw law, $E$ a finite nonempty strict-ranking profile, $v$ a voter, and $c$ a candidate. For any lottery $P$, put $b=\sum_{j:c\succ_v j}P(j)$ and $z=P(c)$. The operational independent-draw probability satisfies
--   $$L_{v,c}(P)=\int_0^1\phi_D(b+sz)\,ds.$$
--   When $z>0$, it also satisfies
--   $$L_{v,c}(P)=\frac1z\int_b^{b+z}\phi_D(u)\,du.$$
--   The map $P\mapsto L_{v,c}(P)$ is continuous and convex on the whole probability simplex, including its boundary. No moment condition is imposed on $D$.
--
--   This identifies the probabilistic comparison with an analytic expression and states the regularity needed by the existence theorem.
--
--   Differences from the source:
--   - encoding: finite nonempty voter and candidate sets with strict rankings → finite nonempty types and Election strict total orders; reason: these represent exactly the finite profiles in Section 2, with uniform voter averaging
--   - encoding: a positive-integer-valued random variable D → a PMF on the positive integers; reason: only the law enters these claims; countably infinite support and infinite mean remain allowed
-- source:
--   Nisarg Shah, Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission #1342 (October 2026), p. 9, Lemma 1.

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankBlocks

set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion

namespace RandomSizeStable.Stability

/-- Lemma 1, p.9: both formulas and regularity on the whole simplex. -/
theorem lemma_1 {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]
    (D : PMF ℕ+) (E : Election V C) (v : V) (c : C) :
    (∀ P ∈ stdSimplex ℝ C,
      comparison D E P v c =
        ∫ s in (0 : ℝ)..1, pgf D (leftRank E P v c + s * P c)) ∧
    (∀ P ∈ stdSimplex ℝ C, 0 < P c →
      comparison D E P v c = (P c)⁻¹ *
        ∫ u in (leftRank E P v c)..(leftRank E P v c + P c), pgf D u) ∧
    ContinuousOn (fun P => comparison D E P v c) (stdSimplex ℝ C) ∧
    ConvexOn ℝ (stdSimplex ℝ C) (fun P => comparison D E P v c) := by sorry

end RandomSizeStable.Stability
