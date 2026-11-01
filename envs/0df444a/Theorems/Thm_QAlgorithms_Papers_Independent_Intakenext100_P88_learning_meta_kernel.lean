-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P88_learning_meta_kernel
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P88.learning_meta_kernel
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:28:15.270846+00:00
-- url     : https://prove2.me/theorems/2bed089a-bce7-4d46-a083-608a3c65c30c
-- title:
--   Leading expectation-value quantum meta-kernel with corrected circuit coefficient
-- statement:
--   The circuit acts on a nonzero finite-dimensional complex Hilbert space $H=\mathbb C^h$ and has the ordered form $U(\theta)=\prod_{\ell=1}^L W_\ell\exp(i\theta_\ell X_\ell)$, with fixed unitary $W_\ell$, Hermitian $X_\ell$, and real angles. Products are written in increasing index order and the rightmost factor acts first. Feature vectors $\phi(x)$ have norm one. For Hermitian observables $O_i$, put $z_{x,i}(\theta)=\langle U(\theta)\phi(x),O_iU(\theta)\phi(x)\rangle\in\mathbb R$.
--
--   Absorb the reference angles into the fixed gates and set $\theta=\delta\varphi$, where $\delta>0$. Write $J_{a\ell}=\partial_{\varphi_\ell}z_a(0)$ and $H_{a,k\ell}=\partial_{\varphi_k}\partial_{\varphi_\ell}z_a(0)$ for derivatives of the actual circuit. The frozen kernel is $K_{ab}=\sum_\ell J_{a\ell}J_{b\ell}$.
--
--   For general data-observable indices $a,b,c$, let $\Theta_{a\ell}$ be the zero-angle commutator expectation defined using the ordered circuit prefixes and suffixes. Let $G_{a,k\ell}=-\partial_{\theta_k}\partial_{\theta_\ell}z_a(0)$ be the unscaled mixed Taylor coefficient of that same circuit. Then
--   $$
--   \mu_{abc}:=\sum_{k,\ell}H_{a,k\ell}J_{bk}J_{c\ell}
--   =\delta^4\sum_{k,\ell}\Theta_{bk}\Theta_{c\ell}G_{a,k\ell}.
--   $$
--   The identity concerns jets at the expansion point. It identifies the leading meta-kernel without asserting suppression of a changing kernel or an unsupported remainder bound.
--
--   Source correction: let $U_0=\prod_\ell W_\ell$, $S_\ell=\prod_{r>\ell}W_r$, $A_a=U_0^\dagger O_aU_0$ and $Y_\ell=S_\ell^\dagger X_\ell S_\ell$. The coefficient is explicitly $G_{a,k\ell}=\langle\phi_a|[Y_{\max(k,\ell)},[Y_{\min(k,\ell)},A_a]]|\phi_a\rangle$. This replaces the faulty interval conjugations of Eq.(40), preserving the Hessian relation in SM Eq.(126); it is not defined by a derivative.
-- source:
--   Representation Learning via Quantum Neural Tangent Kernels, arXiv:2111.04225v3, PDF p. 7, Eq.(45); SM Eqs.(126)-(127)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P88

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder

open MeasureTheory ProbabilityTheory Filter

/-- PDF p.7 Eq.(45), SM p.28 Eqs.(126)-(127): corrected explicit circuit identity.
Printed: G is the interval-commutator coefficient of Eq.(40)/(109).
Changed: G uses the explicit suffix-conjugated nested commutator in gCoefficient.
Why: the printed coefficient disagrees with the original circuit already for one layer
W=H, X=Z, O=Z, phi=|+>. The replacement restores Eq.(126), including equal indices.
Two -i first-derivative factors and the negative Hessian give positive delta^4.
The corrected coefficient and its sign require independent review in the next round. -/
theorem learning_meta_kernel {D I : Type*} {h L : ℕ}
    (M : ExpectationNetwork D I h L) (delta : ℝ) (hdelta : 0 < delta)
    (a b c : D × I) :
    (metaKernel M delta a b c : ℂ) = (delta : ℂ) ^ 4 *
      ∑ k, ∑ l, thetaCoefficient M 0 b k * thetaCoefficient M 0 c l *
        gCoefficient M a k l := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P88

end
