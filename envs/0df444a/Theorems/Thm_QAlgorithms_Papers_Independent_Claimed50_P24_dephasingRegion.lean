-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P24_dephasingRegion
-- name    : QAlgorithms.Papers.Independent.Claimed50.P24.dephasingRegion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:46:10.938984+00:00
-- url     : https://prove2.me/theorems/cd19b379-4544-4ef0-a808-b4f5f4ba284b
-- title:
--   The analytic qubit dephasing region
-- statement:
--   Let $\mathcal C(\mathcal N)\subseteq\mathbb R^3$ be the closure of net triples $(R,P,S)$ achievable with vanishing full trace-norm error by finite block protocols using independent channel copies, forward noiseless public and private classical communication, and initially uniform shared secret key. Generated and consumed rates are separately finite and fixed before the error tolerances. Positive net rates mean generation. The uniform private message and generated secret key must be jointly recovered and decoupled from all public data, the full channel environment, and explicitly discarded local systems. Local memory and operations are free; there is no feedback or prior entanglement.
--
--   Let $p\in[0,1]$ and $\mathcal N_p(\rho)=(1-p)\rho+p\Delta(\rho)$ on a qubit, where $\Delta$ completely dephases the computational basis. Write $H_2(t)=-t\log_2t-(1-t)\log_2(1-t)$ and
--   $$
--   \gamma(\nu,p)=\frac12+\frac12\sqrt{1-16\frac p2\left(1-\frac p2\right)\nu(1-\nu)}.
--   $$
--   A real triple belongs to $\mathcal C(\mathcal N_p)$ exactly when there is one common $\nu\in[0,1/2]$ such that
--   $$
--   R+P\le1,\qquad P+S\le H_2(\nu)-H_2(\gamma(\nu,p)),\qquad R+P+S\le1-H_2(\gamma(\nu,p)).
--   $$
--   The parameter $p$ is the weight of complete dephasing, corresponding to phase-flip probability $p/2$. This gives the entire consuming and generating region.
-- source:
--   Public and private resource trade-offs for a quantum channel, arXiv:1005.3818v3, PDF p. 17, Theorem 4

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P24

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P24

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel erasureDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I B E J D F : Type}

variable [Fintype I] [Fintype B] [Fintype E] [Fintype J] [Fintype D] [Fintype F]

variable [DecidableEq I] [DecidableEq B] [DecidableEq E]

variable [DecidableEq J] [DecidableEq D] [DecidableEq F]

variable [Nonempty I] [Nonempty B] [Nonempty E]

variable [Nonempty J] [Nonempty D] [Nonempty F]

/-- Theorem 4, PDF p.17 (proof pp.20--21): common nu in all three inequalities,
p is the coefficient of complete dephasing, and gamma has p/2 in its radicand. -/
theorem dephasingRegion (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    privateDynamicRegion (dephasingDilation p) = {r | ∃ nu : ℝ, nu ∈ Set.Icc 0 (1 / 2) ∧
      r 0 + r 1 ≤ 1 ∧
      r 1 + r 2 ≤ binEntropy2 nu - binEntropy2 (dephasingGamma nu p) ∧
      r 0 + r 1 + r 2 ≤ 1 - binEntropy2 (dephasingGamma nu p)} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P24

end
