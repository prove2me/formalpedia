-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P03_generalized_inverse_sandwich_bound
-- name    : QAlgorithms.Papers.Independent.Frontier18.P03.generalized_inverse_sandwich_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:31:27.337979+00:00
-- url     : https://prove2.me/theorems/c1ce526f-10d9-4587-b904-a2a377241ec4
-- title:
--   Generalized inverse square-root operator inequality
-- statement:
--   Let $S,T$ be bounded operators on an arbitrary complex Hilbert space, with $0\le S\le I$ and $T\ge0$, and let $c>0$. Set $R_k=(S+T+(k+1)^{-1}I)^{-1/2}$. There is a bounded operator $K$ such that $R_kSR_k v\to Kv$ for every vector $v$, and $$I-K\le(1+c)(I-S)+(2+c+c^{-1})T.$$ Here $K$ is precisely the bounded support extension of $(\sqrt{S+T})^{-1}S(\sqrt{S+T})^{-1}$; the generalized inverse vanishes on the kernel and may itself be unbounded.
--
--   The inequality controls square-root decoding errors without a commutativity or finite-rank assumption.
--
--   **Formalization Note** Operator order is expressed by its inequality on every quadratic form. The existential operator and its strong-limit condition specify the sandwich without pretending that the generalized inverse is bounded.
-- source:
--   General formulas for capacity of classical-quantum channels, arXiv:quant-ph/0206186v4, PDF p. 9, Lemma 2, (15); continuation p.10

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P03

noncomputable section

open Filter

namespace QAlgorithms.Papers.Independent.Frontier18.P03

/-- Lemma 2, PDF pp.9–10, (15). The bounded operator K is the sandwich
specified by its strong regularization limit, not a bounded pseudoinverse.
The final inequality is exactly the source's operator inequality, tested on
every vector. No commutation, finite rank or finite dimension is assumed. -/
theorem generalized_inverse_sandwich_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S T : H →L[ℂ] H) (hS : OperatorPositive S)
    (hSI : OperatorPositive (1 - S)) (hT : OperatorPositive T)
    (c : ℝ) (hc : 0 < c) :
    ∃ K : H →L[ℂ] H,
      (∀ v, Tendsto (fun k : ℕ => regularizedSandwich S T k v) atTop (nhds (K v))) ∧
      ∀ v, ‖v‖ ^ 2 - (inner ℂ v (K v)).re ≤
        (1 + c) * (‖v‖ ^ 2 - (inner ℂ v (S v)).re) +
        (2 + c + c⁻¹) * (inner ℂ v (T v)).re := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P03

end
