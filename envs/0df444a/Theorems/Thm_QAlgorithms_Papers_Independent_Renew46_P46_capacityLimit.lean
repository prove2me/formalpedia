-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P46_capacityLimit
-- name    : QAlgorithms.Papers.Independent.Renew46.P46.capacityLimit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:48:41.865709+00:00
-- url     : https://prove2.me/theorems/2ec676fe-bb54-451b-a311-858d1c8adf28
-- title:
--   §I: superadditivity and existence of the capacity limit, (4)–(5)
-- statement:
--   Let $S_i$ be normalized positive trace-class signal states on any complex Hilbert space. For a real cost $f$ and budget $E$, assume that an affordable symbol exists. Let $C_n$ be the supremum of the Shannon information in nats over all input probability laws on words of length $n$ with defined finite expected total cost at most $nE$, and over all discrete collective output measurements. Then, for positive integers $n,m$,
--
--   $$C_n+C_m\le C_{n+m},\qquad \lim_{n\to\infty}\frac{C_n}{n}=C\in[0,\infty].$$
--
--   The limit is in the nonnegative extended reals and may be infinite. This foundational result does not assume the later finite-capacity convention.
-- source:
--   On Quantum Communication Channels with Constrained Inputs, arXiv:quant-ph/9705054v1, PDF p. 2, §I: superadditivity and existence of the capacity limit, (4)–(5)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P46

open Filter MeasureTheory QAlgorithms.RealRegisters

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Unnumbered result, PDF p.2, (4)-(5). This precedes the finite-capacity
restriction: the limit can equal infinity. -/
theorem capacityLimit {I A : Type} (S : A → constrainedCqState I) (f : A → ℝ) (E : ℝ)
    (hfeasible : ∃ a, f a ≤ E) :
    (∀ n m : ℕ, 0 < n → 0 < m →
      constrainedCqBlockCapacity S f E n + constrainedCqBlockCapacity S f E m ≤ constrainedCqBlockCapacity S f E (n + m)) ∧
    Tendsto (fun n : ℕ => constrainedCqBlockCapacity S f E (n + 1) / (n + 1 : ℕ)) atTop
      (𝓝 (constrainedCqCapacity S f E)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P46

end
