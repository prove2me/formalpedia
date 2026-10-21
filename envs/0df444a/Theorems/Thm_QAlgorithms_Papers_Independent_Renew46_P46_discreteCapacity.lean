-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P46_discreteCapacity
-- name    : QAlgorithms.Papers.Independent.Renew46.P46.discreteCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:47:44.770998+00:00
-- url     : https://prove2.me/theorems/8e3c534c-a3b0-4e7b-bce2-7277f583a9ef
-- title:
--   Proposition 2: constrained discrete classical–quantum capacity, (10)
-- statement:
--   Let $S_i$ be normalized positive trace-class states on an arbitrary complex Hilbert space, indexed by a discrete alphabet $A$. Let $f:A\to\mathbb R$ be the cost, $E\in\mathbb R$ the budget, and assume some symbol has cost at most $E$. Write $\mathcal P_1$ for probability laws with a defined finite cost expectation at most $E$, $\bar S_\pi=\sum_i\pi_iS_i$, and $H$ for extended von Neumann entropy in nats. Let $C<\infty$ be the regularized measured capacity of the memoryless product-signal channel, with ensemble-average block cost at most $nE$. If $\sup_{\pi\in\mathcal P_1}H(\bar S_\pi)<\infty$, then
--
--   $$C=\sup_{\pi\in\mathcal P_1}\left[H(\bar S_\pi)-\sum_i\pi_iH(S_i)\right].$$
--
--   This is the constrained classical–quantum capacity theorem; it assumes neither entropy additivity nor the existence of good codes.
-- source:
--   On Quantum Communication Channels with Constrained Inputs, arXiv:quant-ph/9705054v1, PDF p. 3, Proposition 2: constrained discrete classical–quantum capacity, (10)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P46

open Filter MeasureTheory QAlgorithms.RealRegisters

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Proposition 2, PDF p.3, (10); standing assumptions pp.1-3. The capacity is
measured/regularized, signals are product cq outputs, and (8) is a uniform
entropy bound. No additivity or coding theorem is assumed. -/
theorem discreteCapacity {I A : Type} (S : A → constrainedCqState I) (f : A → ℝ) (E : ℝ)
    (hfeasible : ∃ a, f a ≤ E)
    (hbound : EntropyBound (fun a => (S a).val) f E)
    (hfinite : constrainedCqCapacity S f E < ⊤) :
    constrainedCqCapacity S f E = ⨆ pi : {pi : PMF A // constrainedCqAdmissible f E pi},
      discreteChi (fun a => (S a).val) pi.val := by sorry

end QAlgorithms.Papers.Independent.Renew46.P46

end
