-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P58_noFeedbackNormalApproximation
-- name    : QAlgorithms.Papers.Independent.Information100.P58.noFeedbackNormalApproximation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:20:02.838592+00:00
-- url     : https://prove2.me/theorems/4be01683-ff84-45d9-a9b4-b6c98334e64c
-- title:
--   Common no-feedback normal approximation with bounded remainder
-- statement:
--   Fix an integer $d\ge2$ and $p,\varepsilon\in(0,1)$. For each positive blocklength $n$, let $C_{n,\varepsilon}$ be the base-two logarithm of the largest message count attainable at error tolerance $\varepsilon$. Consider all four choices: classical or unrestricted quantum no-feedback codes, and average or maximum error, with no shared randomness. Writing $\Phi^{-1}$ for the standard-normal quantile, there is one finite $A\ge0$, depending only on $d,p,\varepsilon$, such that all four capacities satisfy
--
--   $$\left|C_{n,\varepsilon}-n(1-p)\log_2d-\sqrt{np(1-p)}\log_2d\,\Phi^{-1}(\varepsilon)\right|\le A\quad(n\ge1).$$
--
--   The error is uniformly bounded at every positive blocklength; no convergence of the remainder is asserted.
-- source:
--   Finite-blocklength classical communication over the quantum erasure channel with and without classical feedback, arXiv:2610.00440v1, PDF p. 35, Corollary 8.4

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

namespace QAlgorithms.Papers.Independent.Information100.P58

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

/-- Corollary 8.4, PDF pp.35–36: uniform bounded remainder for all four no-feedback capacities. -/
theorem noFeedbackNormalApproximation (d : ℕ) (hd : 2≤d) (p ε : ℝ)
    (hp0 : 0<p) (hp1 : p<1) (hε0 : 0<ε) (hε1 : ε<1) :
    ∃ A : ℝ, 0≤A ∧ ∀ n : ℕ, 0<n → ∀ classical worst : Bool,
      |capacity n d p ε classical worst - normalCenter n d p ε| ≤ A := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P58
