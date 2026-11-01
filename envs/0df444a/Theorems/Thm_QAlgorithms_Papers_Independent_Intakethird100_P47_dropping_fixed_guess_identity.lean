-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P47_dropping_fixed_guess_identity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P47.dropping_fixed_guess_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:36:23.400261+00:00
-- url     : https://prove2.me/theorems/c659f13a-6987-4d9f-8c04-6f69f8ce6c97
-- title:
--   Balance and fixed-guess score after dropping
-- statement:
--   Work in the accepted-round law of Alice's key bit $A$ and a fixed Eve guess $G$. Let $p_0,p_1\ge0$ sum to one and let $P_0,P_1\in[0,1]$. Their joint probabilities are $J(0,0)=p_0P_0$, $J(1,0)=p_0(1-P_0)$, $J(0,1)=p_1(1-P_1)$, and $J(1,1)=p_1P_1$. Define $u_0=p_0P_0+p_1(1-P_1)>0$ and $u_1=p_0(1-P_0)+p_1P_1>0$. Independently retain bit $k$ with probability $k_k=\min(u_0,u_1)/u_k$. These are valid positive retention probabilities at most one, and
--   $$
--   \Pr[\mathrm{keep}]=2\min(u_0,u_1),\qquad
--   \Pr[A=k\mid\mathrm{keep}]=\tfrac12,
--   $$
--   $$
--   \Pr[G=A\mid\mathrm{keep}]
--   =\frac12\left(\frac{p_0P_0}{u_0}+\frac{p_1P_1}{u_1}\right).
--   $$
--   If $u_0=u_1$, every round is retained. Zero-mass guess groups contribute zero. This is the score of the same fixed guess after conditioning on the keep flag.
-- source:
--   Device-independent quantum key distribution based on measurement inputs, arXiv:1308.6447v3, PDF p. 8, VI B: balancing and fixed-strategy score after dropping

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

namespace QAlgorithms.Papers.Independent.Intakethird100.P47

open scoped ComplexConjugate

open scoped BigOperators

/-- VI B, PDF p.8: exact balancing, retention yield, and fixed-guess success after dropping.
Group weights are conditioned on S. The result does not optimize Eve after the public keep flag. -/
theorem dropping_fixed_guess_identity (p0 p1 P0 P1 : ℝ)
    (hp0 : 0 ≤ p0) (hp1 : 0 ≤ p1) (hp : p0 + p1 = 1)
    (hP0 : 0 ≤ P0 ∧ P0 ≤ 1) (hP1 : 0 ≤ P1 ∧ P1 ≤ 1)
    (hu0 : 0 < p0 * P0 + p1 * (1 - P1))
    (hu1 : 0 < p0 * (1 - P0) + p1 * P1) :
    let j := guessLaw p0 p1 P0 P1
    let u0 := aliceMarginal j false
    let u1 := aliceMarginal j true
    let k := balanceRetention j
    IsPairLaw j ∧
    u0 = p0 * P0 + p1 * (1 - P1) ∧ u1 = p0 * (1 - P0) + p1 * P1 ∧
    (∀ A, 0 < k A ∧ k A ≤ 1) ∧
    retention j k = 2 * min u0 u1 ∧ 0 < retention j k ∧
    (∀ A, aliceMarginal (retainedLaw j k) A = 1 / 2) ∧
    (∑ A, retainedLaw j k A A) = (1 / 2) * (p0 * P0 / u0 + p1 * P1 / u1) ∧
    (u0 = u1 → ∀ A, k A = 1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P47
