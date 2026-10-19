-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P58_noFeedbackReliabilityBounds
-- name    : QAlgorithms.Papers.Independent.Information100.P58.noFeedbackReliabilityBounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:23:09.308201+00:00
-- url     : https://prove2.me/theorems/bf1f6858-783e-4280-9a55-36ee16f5ad7d
-- title:
--   No-feedback reliability bounds and exact high-rate exponent
-- statement:
--   Fix $d\ge2$, $0<p<1$, $q=1-p$ and $0<R<q\log_2 d$. Put $M_n=\lceil2^{nR}\rceil$, $R_{\rm crit}=q\log_2d/(q+dp)$, $D(t\Vert q)=t\log_2(t/q)+(1-t)\log_2((1-t)/(1-q))$ with continuous endpoints, $E_r(R)=\min_{0\le t\le1}[D(t\Vert q)+(t\log_2d-R)_+]$, and $E_{\rm ex}(R)=\sup_{s\ge1}[-s\log_2(1/d+(1-1/d)p^{1/s})-sR]$, where $s$ is real. For each of classical and unrestricted quantum no-feedback coding, and each of average and maximum error without shared randomness, let $e_n=-\log_2\varepsilon^*(n,M_n)/n$ be computed from its operational optimal error. Then
--
--   $$\max\{E_r(R),E_{\rm ex}(R)\}\le\liminf e_n\le\limsup e_n\le D(R/\log_2d\Vert q).$$
--
--   The random-coding minimum is attained and equals $-\log_2(p+q/d)-R$ when $R\le R_{\rm crit}$, and $D(R/\log_2d\Vert q)$ when $R\ge R_{\rm crit}$. In the latter range every sequence $e_n$ converges to this value. No low-rate convergence is asserted.
-- source:
--   Finite-blocklength classical communication over the quantum erasure channel with and without classical feedback, arXiv:2610.00440v1, PDF p. 40, Proposition 8.7

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

namespace QAlgorithms.Papers.Independent.Information100.P58

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

/-- Proposition 8.7, PDF pp.39–40: all four no-feedback reliability bounds and the exact
high-rate limit, without shared randomness. The common numerical value is the feedback
exponent of Corollary 8.6; that operational feedback theorem remains separately deferred.
No limit is asserted below the critical rate. -/
theorem noFeedbackReliabilityBounds (d : ℕ) (hd : 2 ≤ d) (p R : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hR0 : 0 < R) (hR1 : R < (1-p)*Real.logb 2 d) :
    (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ randomCodingExponent d p R =
      binaryRelativeEntropy t (1-p) + max (t*Real.logb 2 d-R) 0) ∧
    (R ≤ criticalRate d p → randomCodingExponent d p R =
      -Real.logb 2 (p+(1-p)/(d : ℝ))-R) ∧
    (criticalRate d p ≤ R → randomCodingExponent d p R =
      binaryRelativeEntropy (R/Real.logb 2 d) (1-p)) ∧
    ∀ classical worst : Bool,
      max (randomCodingExponent d p R) (expurgatedExponent d p R) ≤
        Filter.liminf (noFeedbackErrorDecay d p R classical worst) Filter.atTop ∧
      Filter.liminf (noFeedbackErrorDecay d p R classical worst) Filter.atTop ≤
        Filter.limsup (noFeedbackErrorDecay d p R classical worst) Filter.atTop ∧
      Filter.limsup (noFeedbackErrorDecay d p R classical worst) Filter.atTop ≤
        binaryRelativeEntropy (R/Real.logb 2 d) (1-p) ∧
      (criticalRate d p ≤ R →
        Filter.Tendsto (noFeedbackErrorDecay d p R classical worst) Filter.atTop
          (nhds (binaryRelativeEntropy (R/Real.logb 2 d) (1-p)))) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P58
