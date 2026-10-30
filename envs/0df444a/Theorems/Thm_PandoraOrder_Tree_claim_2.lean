-- Prove2me | Theorems.Thm_PandoraOrder_Tree_claim_2
-- name    : PandoraOrder.Tree.claim_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T22:01:59.648114+00:00
-- url     : https://prove2.me/theorems/d7e77eb2-241f-4985-88a2-f31d26828e4c
-- title:
--   Claim 2 — generalized reservation values are well posed and give indifference
-- statement:
--   Let $b::L$ be any nonempty line of distinct boxes in the finite-support source model. For every nonnegative incumbent, the semantic value supremum is bounded and attained by a deterministic adaptive stopping policy. Let $z$ be the infimum of the nonnegative zeros of $\Phi(x,b::L)-x$. Then
--   $$z=\min\{x\ge0:\Phi(x,b::L)=x\}.$$
--   Every optimal stopping choice has expected excess payoff $\Phi(x,b::L)-x$, so the zero condition is independent of that choice. If $z>0$, some optimal deterministic policy at $z$ opens $b$ rather than stopping. Finally, without a positivity qualification, the optimal value among policies required to open $b$ is $z$, equal to the value of stopping.
--
--   This preserves all three clauses of the printed claim. The final clause is false on the source-legal singleton $X=0,c=1$: the threshold is zero but opening gives minus one. That finding is recorded separately in INSIGHTS.yaml; the item does not replace it with a positive-threshold-only assertion.
--
--   Differences from the source:
--   - encoding: independent finite-support nonnegative box rewards and nonnegative costs → Fin-indexed boxes and atom tables with real masses, allowing repeated atoms and zero masses, and real nonnegative costs; reason: finite sums give the same product experiment; no rationality, common grid, positivity of costs, or normalization is imposed
--   - reading: page 7 conditions on reaching an incumbent, while Appendix C evaluates every nonnegative incumbent → restart the remaining suffix with its independent future laws and a specified incumbent; reason: this preserves the off-support incumbents required by equation (9) and exact threshold computation
--   - encoding: optimal stopping times and the smallest solution of equation (2) → actual-policy value suprema, deterministic attainment, a least-root assertion and equality of every optimal excess payoff; reason: finite-horizon histories encode stopping times; the final indifference assertion remains unconditional
-- source:
--   Boodaghians et al., arXiv:2002.06968v2, Claim 2, p. 8 (PDF p. 8); https://arxiv.org/abs/2002.06968v2

import Definitions.Def_PandoraOrder_Tree_Contracts

namespace PandoraOrder.Tree

theorem claim_2 {n : ℕ} (I : Instance n) (b : Fin n) (L : List (Fin n))
    (hL : (b :: L).Nodup) :
    IsLeast {x : ℝ | 0 ≤ x ∧ lineValue I (b :: L) x = x} (threshold I (b :: L)) ∧
    (∀ x : ℝ, 0 ≤ x →
      BddAbove {v | ∃ π : Policy n, Admissible (lineConstraint (b :: L)) π ∧
        value I π x = v} ∧
      (∃ π : Policy n, Admissible (lineConstraint (b :: L)) π ∧ Deterministic π ∧
        value I π x = lineValue I (b :: L) x) ∧
      (∀ π : Policy n, Admissible (lineConstraint (b :: L)) π →
        value I π x = lineValue I (b :: L) x →
        (value I π x - x = 0 ↔ lineValue I (b :: L) x = x))) ∧
    (0 < threshold I (b :: L) →
      ∃ π : Policy n, Admissible (lineConstraint (b :: L)) π ∧ Deterministic π ∧
        (π []).prob (some b) = 1 ∧
        value I π (threshold I (b :: L)) = threshold I (b :: L)) ∧
    openingValue I b L (threshold I (b :: L)) = threshold I (b :: L) := by sorry

end PandoraOrder.Tree
