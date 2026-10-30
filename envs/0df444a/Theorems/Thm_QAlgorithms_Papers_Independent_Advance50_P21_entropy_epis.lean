-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P21_entropy_epis
-- name    : QAlgorithms.Papers.Independent.Advance50.P21.entropy_epis
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:49:39.984008+00:00
-- url     : https://prove2.me/theorems/34fb0323-d0c2-4299-8d13-c67e1ed1edb6
-- title:
--   Corollary 7: qudit entropy EPI, entropy-power EPI, and EPnI
-- statement:
--   Let $d\ge2$, let $\rho,\sigma$ be positive semidefinite complex $d\times d$ matrices of trace one, and let $a\in[0,1]$. Write
--   $$
--   \rho\boxplus_a\sigma=a\rho+(1-a)\sigma-i\sqrt{a(1-a)}(\rho\sigma-\sigma\rho).
--   $$
--
--   Define $E_c(\tau)=e^{cH(\tau)}$ and $N_c(\tau)=g^{-1}(cH(\tau))$. Then all three inequalities hold:
--   $$\begin{aligned}
--   H(\rho\boxplus_a\sigma)&\ge aH(\rho)+(1-a)H(\sigma),\\
--   E_c(\rho\boxplus_a\sigma)&\ge aE_c(\rho)+(1-a)E_c(\sigma)&&[0\le c\le(\log d)^{-2}],\\
--   N_c(\rho\boxplus_a\sigma)&\ge aN_c(\rho)+(1-a)N_c(\sigma)&&[0\le c\le(d-1)^{-1}].
--   \end{aligned}$$
--   Here $H(\rho)=-\operatorname{Tr}(\rho\log\rho)$ is the von Neumann entropy in nats, with zero-weight terms defined by continuity. Write $g(x)=(x+1)\log(x+1)-x\log x$ for $x\ge0$, and let $g^{-1}$ be its inverse from nonnegative entropies to nonnegative occupations.
--   These are respectively the entropy EPI, entropy-power EPI, and entropy photon-number inequality. No commutation hypothesis is imposed.
-- source:
--   Entropy power inequalities for qudits, arXiv:1503.04213v3, PDF p. 7, Corollary 7: qudit entropy EPI, entropy-power EPI, and EPnI

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P21

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (simplex orderedSpectrum majorizedBy)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble)

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

/-- PDF p.7, Corollary 7, (3.6)–(3.8): all three qudit EPIs; inputs need not commute. -/
theorem entropy_epis {d : ℕ} (hd : 2 ≤ d) (rho sigma : Mat d)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    (a * entropy rho + (1 - a) * entropy sigma ≤ entropy (quditAddition a rho sigma)) ∧
    (∀ c : ℝ, 0 ≤ c → c ≤ 1 / (Real.log (d : ℝ)) ^ 2 →
      a * quditEntropyPower c rho + (1 - a) * quditEntropyPower c sigma ≤
        quditEntropyPower c (quditAddition a rho sigma)) ∧
    (∀ c : ℝ, 0 ≤ c → c ≤ 1 / ((d : ℝ) - 1) →
      a * quditEntropyPhotonNumber c rho + (1 - a) * quditEntropyPhotonNumber c sigma ≤
        quditEntropyPhotonNumber c (quditAddition a rho sigma)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P21

end
