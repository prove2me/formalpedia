-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P46_operationalCapacity
-- name    : QAlgorithms.Papers.Independent.Renew46.P46.operationalCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:49:31.093318+00:00
-- url     : https://prove2.me/theorems/af474c96-cb24-4f09-a87a-d53478d07ed2
-- title:
--   Proposition 1: operational coding characterization and weak converse
-- statement:
--   Consider a memoryless classical–quantum channel with normalized positive trace-class signals, real cost $f$, budget $E$, an affordable symbol, and finite regularized measured capacity $C$ in nats. For integers $n,M\ge1$, let $p(n,M)$ be the infimum of uniform-message average error over $M$-message collective-measurement codes whose every word has total cost at most $nE$; erasure counts as error. For $R\ge0$, set $M_n=\max\{1,\lfloor e^{nR}\rfloor\}$. Then
--
--   $$R<C\ \Longrightarrow\ p(n,M_n)\to0,\qquad R>C\ \Longrightarrow\ p(n,M_n)\not\to0.$$
--
--   This is an operational characterization with a weak converse. The paper attributes it to Gallager [4], Section 7.3; it does not assert an optimizing code exists.
-- source:
--   On Quantum Communication Channels with Constrained Inputs, arXiv:quant-ph/9705054v1, PDF p. 3, Proposition 1: operational coding characterization and weak converse

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P46

open Filter MeasureTheory QAlgorithms.RealRegisters

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Proposition 1, PDF p.3, both directions; attributed there to Gallager [4],
Section 7.3. This is a weak converse, without claiming error tends to one.
The source's exponential message count is rounded to a positive integer. -/
theorem operationalCapacity {I A : Type} (S : A → constrainedCqState I) (f : A → ℝ) (E : ℝ)
    (hfeasible : ∃ a, f a ≤ E) (hfinite : constrainedCqCapacity S f E < ⊤) :
    ∀ R : ℝ, 0 ≤ R →
      (ENNReal.ofReal R < constrainedCqCapacity S f E →
        Tendsto (fun n : ℕ => constrainedCqError S f E (n + 1) (constrainedCqMessages (n + 1) R)) atTop (𝓝 0)) ∧
      (constrainedCqCapacity S f E < ENNReal.ofReal R →
        ¬ Tendsto (fun n : ℕ => constrainedCqError S f E (n + 1) (constrainedCqMessages (n + 1) R)) atTop (𝓝 0)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P46

end
