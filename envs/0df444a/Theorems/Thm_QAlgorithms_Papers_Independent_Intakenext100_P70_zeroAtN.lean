-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P70_zeroAtN
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P70.zeroAtN
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:43:12.98173+00:00
-- url     : https://prove2.me/theorems/26e30973-f982-48b0-bdc6-bc083bbbca32
-- title:
--   Zero optimized coherent information at n uses
-- statement:
--   Let the main input and output be equal positive finite-dimensional registers in fixed computational bases, and let $\Gamma$ be a completely positive trace-preserving PPT-binding channel between them, meaning that its Choi matrix has positive partial transpose on the output. Let $n\geq1$, $0\leq\kappa\leq1$, and
--   $$
--   (1+\kappa^n)^{-1/n}\leq p\leq1.
--   $$
--   Define $\mathcal M$ exactly as in (S15): the retained binary switch chooses between $\mathcal E_\kappa\circ\Gamma$ and $\mathcal E_p$, with erasure of the entire main register and a separate flag. Then
--   $$
--   Q^{(n)}(\mathcal M)=\frac1n\max_{\rho}I_{\mathrm{coh}}(\mathcal M^{\otimes n},\rho)=0.
--   $$
--   The maximum is over all joint density inputs, including entangled inputs and coherent switch inputs. The endpoint $p=1$ is included in this lemma; when $\kappa=0$ the hypothesis forces $p=1$.
--
--   The result supplies the finite-block obstruction independently of the special Choi-state construction.
-- source:
--   Unbounded number of channel uses are required to see quantum capacity, arXiv:1408.5115v1, PDF p. 8, Supplementary Lemma 3, Eqs. (S40)–(S43)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P70

namespace QAlgorithms.Papers.Independent.Intakenext100.P70

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22
  (Op coherentInformation singleUseInformation quantumCapacity mixed)

/-- Supplementary Lemma 3, PDF pp.8--9, S40--S43: the exact optimized coherent information
of n uses is zero, for any finite equal-port PPT-binding Gamma. Here the closed p=1 endpoint
is valid; kappa=0 forces p=1. All entangled n-use inputs are included. -/
theorem zeroAtN {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (Gamma : Superop I I) (hGamma : CubittPPTBinding Gamma)
    (n : ℕ) (hn : 0 < n) (kappa p : ℝ)
    (hk0 : 0 ≤ kappa) (hk1 : kappa ≤ 1)
    (hp0 : cubittErasureThreshold n kappa ≤ p) (hp1 : p ≤ 1) :
    cubittBlockInformation (cubittNoisySwitch Gamma kappa p) n = 0 := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P70
