-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_theta_inequalities
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.theta_inequalities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:19:32.005314+00:00
-- url     : https://prove2.me/theorems/18732d85-bb2f-4af8-9354-26f192b3fbf9
-- title:
--   Lemma 13: theta-function inequalities, Eqs.(D.41)–(D.42), convergent domain
-- statement:
--   Let $0<q<1$ and $z=ib$ with $b\ge0$. In the source’s nome convention, $\vartheta_3(z,q)=\sum_{k\in\mathbb Z}q^{k^2}e^{2ikz}$ and $\vartheta_2(0,q)=\sum_{k\in\mathbb Z}q^{(k+1/2)^2}$. These convergent real-valued series satisfy $$\vartheta_3(ib,q)\ge\vartheta_3(0,q),\qquad \vartheta_2(0,q)\ge q^{1/4}\vartheta_3(0,q).$$ These inequalities supply the odd-shift overlap estimate. **Source correction:** the printed endpoint $q=1$ is excluded because the series diverge; independent moderation is still required.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 46, Lemma 13: theta-function inequalities, Eqs.(D.41)–(D.42), convergent domain

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF pp.46–47, Lemma 13. SOURCE CORRECTION: printed q<=1 changed to q<1;
q=1 gives divergent series. b>=0 parametrizes exactly Re(z)=0, Im(z)>=0.
The correction still requires independent moderation. -/
theorem theta_inequalities (q b : ℝ) (hq : 0 < q) (hq1 : q < 1) (hb : 0 ≤ b) :
    theta3Imaginary 0 q ≤ theta3Imaginary b q ∧
    Real.rpow q (1 / 4) * theta3Imaginary 0 q ≤ theta2Zero q := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
