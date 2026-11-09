-- Prove2me | Theorems.Thm_RankingQueryCost_Joint_equation_28
-- name    : RankingQueryCost.Joint.equation_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:26:23.598123+00:00
-- url     : https://prove2.me/theorems/0b31ac06-a2e5-4fb0-a347-c98a1c86f4ac
-- title:
--   Equation (28) — Adaptive excess-weight bound
-- statement:
--   Standing domain: $n\ge16$ is divisible by four, $N=\binom n2$, and the supplied total budget obeys $0\le s\le\lfloor N/32\rfloor$, except for the explicitly generalized band-closure statement. All ranks permute $0,\ldots,n-1$; estimates range over the continuous set $Q$ defined in §2.1.
--
--   Let $0<p\le1$, let $E_0$ be fixed before fresh sampling, and let the new support $F$ be disjoint from $E_0$, with $|E_0\cup F|\le s$ and $|F|\le h$. Write $w_e=I_e/p$ for a mask, and let $|c_e|\le1$. Simultaneously for every mask, support $F$ and coefficient vector,
--
--   $$\left\|\sum_{e\in E_0\cup F}w_ec_ex_e\right\|_2\le\sqrt U+H_{E_0}(w)+(1/p-1)\sqrt{B_h}.$$
--
--   Thus a support chosen after observing the mask is covered. The leading unweighted error is one $\sqrt U$ term for the union, and only the excess weight is charged to the newly designated identities.
--
--   Differences from the source:
--   - encoding: n labelled objects and unordered distinct comparison identities → Fin n labels and increasing representatives of unordered pairs; reason: this is a bijective representation and leaves the estimate space continuous
--   - encoding: incidence vectors oriented by the warm order → incidence vectors oriented by public labels and arbitrary signed coefficients; reason: orientation signs are absorbed by the coefficients, and H uses absolute inner products
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), equation (28), p. 29, PDF p. 30; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Flow

set_option autoImplicit false

namespace RankingQueryCost.Joint

/-- Equation (28), p. 29 / PDF 30. There is one unweighted √U term for the union support.
F may be selected after seeing the mask; the statement is simultaneous over every such F. -/
theorem equation_28 (n s h : ℕ) (hadm : Admissible n s)
    (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (E₀ : Finset (Pair n)) :
    ∀ (mask : Pair n → Bool) (F : Finset (Pair n)), Disjoint E₀ F →
      (E₀ ∪ F).card ≤ s → F.card ≤ h →
      ∀ c : Pair n → ℝ, (∀ e ∈ E₀ ∪ F, |c e| ≤ 1) →
        euclideanNorm (flow (E₀ ∪ F) (fun e => (if mask e then 1 / p else 0) * c e)) ≤
          Real.sqrt (errorScale n s : ℝ) +
          faultyFluctuation E₀ (fun e => if mask e then 1 / p else 0) +
          (1 / p - 1) * Real.sqrt (incidenceCap n h : ℝ) := by sorry

end RankingQueryCost.Joint
