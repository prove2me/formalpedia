-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P25_waitingDistribution
-- name    : QAlgorithms.Papers.Independent.Gap48.P25.waitingDistribution
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:48:44.657845+00:00
-- url     : https://prove2.me/theorems/08c783f1-c96d-4af5-a804-af285ecfd02c
-- title:
--   Appendix B, footnote 75: independent-link waiting distribution and mean
-- statement:
--   Let two links have independent geometric waiting times on positive rounds, each with success probability $0<x\le1$. Write $M$ for their maximum. Its nonnegative normalized distribution and finite mean satisfy, for $n\ge1$,
--
--   $$\Pr(M=n)=x(1-x)^{n-1}[2-(2-x)(1-x)^{n-1}],\qquad \mathbb E[M]={3-2x\over x(2-x)}.$$
--
--   The maximum distribution is constructed directly from the product of the geometric laws, and the expectation is a genuinely summable series. Also $x\mathbb E[M]\to3/2$ as $x\downarrow0$. At $x=1$ the mean is one round. The excluded endpoint $x=0$ has infinite waiting time and is not assigned a real mean by this formula.
-- source:
--   The Security of Practical Quantum Key Distribution, arXiv:0802.4155v3, PDF p. 46, Appendix B, footnote 75: independent-link waiting distribution and mean

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P25

open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- Footnote 75, PDF p.46: exact law and mean of two independent geometric
links. Includes x=1, excludes x=0 from the real expectation formula. -/
theorem waitingDistribution (x : ℝ) (hx : 0 < x ∧ x ≤ 1) :
    (∀ n, 0 ≤ twoLinkWaiting x n) ∧ HasSum (twoLinkWaiting x) 1 ∧
    (∀ n : ℕ, 1 ≤ n → twoLinkWaiting x n = x*(1-x)^(n-1)*(2-(2-x)*(1-x)^(n-1))) ∧
    HasSum (fun n : ℕ => (n : ℝ)*twoLinkWaiting x n) (waitingMean x) ∧
    Tendsto (fun z : ℝ => z*waitingMean z) (nhdsWithin 0 (Set.Ioi 0)) (nhds (3/2)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P25

end
