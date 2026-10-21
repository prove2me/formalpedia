-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P03_continuous_integrated_entropy
-- name    : QAlgorithms.Papers.Independent.Support21.P03.continuous_integrated_entropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:42:18.027705+00:00
-- url     : https://prove2.me/theorems/c3d8d0ba-d598-40cd-b417-58726e9587a9
-- title:
--   Continuous integrated entropy balance and moment formulas
-- statement:
--   Let $(M,\mathcal F,\omega)$ be a probability space and let $\phi^t$ be a group of measurable automorphisms, jointly measurable in time and configuration, with time domain $\mathbb Z$ or $\mathbb R$. Assume that $\omega_t=(\phi^t)_*\omega$ is equivalent to $\omega$ for every time. Set $\ell_t=\log(d\omega_t/d\omega)$ and $c^t=\ell_t\circ\phi^t$. Equalities of observables are modulo $\omega$-null sets. Write $e_t(\alpha)=\log\int e^{\alpha\ell_t}\,d\omega$, retaining extended moment values. A time reversal $\vartheta$ is a measurable involution with $\vartheta\phi^t=\phi^{-t}\vartheta$ and $\vartheta_*\omega=\omega$.
--
--   In continuous time assume (E1): the actual RN densities form a strongly $C^1$ curve in $L^1(\omega)$, and their derivative $\sigma$ at zero has a strongly continuous transported orbit $\sigma_s=\sigma\circ\phi^s$ in $L^1(\omega)$. Write $A_t(x)=\int_0^t\sigma_s(x)\,ds$ and $m_t=t^{-1}\int_0^t\omega(\sigma_s)\,ds$ for $t\ne0$.
--
--   For $t\ne0$, $\Sigma^t=A_t/t$ almost everywhere. For every real $t$ and $\alpha$,
--   $$\operatorname{Ent}(\omega_t\mid\omega)=-\int_0^t\omega(\sigma_s)\,ds,\qquad
--   e_t(\alpha)=\log\omega\left(\exp\left(\alpha\int_0^t\sigma_{-s}\,ds\right)\right).$$
--   If the system is time reversal invariant, also $e_t(\alpha)=\log\omega(e^{-\alpha A_t})$.
--
--   Only the mean requires nonzero time; the exponential moments use extended integration.
-- source:
--   Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, PDF p. 13, continuous-integrated-entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

/-- The explicit continuous integrated-entropy formulas, PDF pp.13--14.
Only the mean formula excludes t=0; exponential moments remain extended-valued. -/
theorem continuous_integrated_entropy (D : RegularSystem M) :
    (∀ t : ℝ, t ≠ 0 → ∀ᵐ x ∂(D.omega : Measure M),
      meanEntropy D.toNonsingularSystem t x = pointMean D t x) ∧
    (∀ t : ℝ, signedEntropy (pushedReference D.toNonsingularSystem t) (D.omega : Measure M) =
      (-(∫ s in 0..t, ∫ x, continuousSigma D (D.flow s x) ∂(D.omega : Measure M)) : ℝ)) ∧
    (∀ t alpha : ℝ, finiteES D.toNonsingularSystem t alpha =
      ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp
        (alpha * (∫ s in 0..t, continuousSigma D (D.flow (-s) x)))) ∂(D.omega : Measure M))) ∧
    (∀ theta : M ≃ᵐ M, IsTimeReversal D.toNonsingularSystem theta →
      ∀ t alpha : ℝ, finiteES D.toNonsingularSystem t alpha =
        ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (-alpha * integratedSigma D t x))
          ∂(D.omega : Measure M))) := by sorry

end QAlgorithms.Papers.Independent.Support21.P03

end
