-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P03_entropy_balance
-- name    : QAlgorithms.Papers.Independent.Support21.P03.entropy_balance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:40:54.119436+00:00
-- url     : https://prove2.me/theorems/d06250b8-445b-4da7-b943-cfe4579c3dbb
-- title:
--   Extended entropy balance and mean-production transport
-- statement:
--   Let $(M,\mathcal F,\omega)$ be a probability space and let $\phi^t$ be a group of measurable automorphisms, jointly measurable in time and configuration, with time domain $\mathbb Z$ or $\mathbb R$. Assume that $\omega_t=(\phi^t)_*\omega$ is equivalent to $\omega$ for every time. Set $\ell_t=\log(d\omega_t/d\omega)$ and $c^t=\ell_t\circ\phi^t$. Equalities of observables are modulo $\omega$-null sets. Write $e_t(\alpha)=\log\int e^{\alpha\ell_t}\,d\omega$, retaining extended moment values. A time reversal $\vartheta$ is a measurable involution with $\vartheta\phi^t=\phi^{-t}\vartheta$ and $\vartheta_*\omega=\omega$.
--
--   Let $\operatorname{Ent}=-D_{\rm KL}$ and use extended signed expectations. Then for every time $t$, $\operatorname{Ent}(\omega_t\mid\omega)=-\omega(c^t)$. For $t\ne0$ set $\Sigma^t=c^t/t$. One has
--   $$\operatorname{Ent}(\omega_t\mid\omega)=-t\omega(\Sigma^t),\qquad
--   \Sigma^t=\Sigma^{-t}\circ\phi^t,$$
--   and $\omega(\Sigma^t)\ge0$ for $t>0$. Under time reversal,
--   $$\Sigma^t\circ\vartheta=-\Sigma^{-t}=-\Sigma^t\circ\phi^{-t}.$$
--
--   Entropy and mean production may be infinite; no integrability assumption is added.
-- source:
--   Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, PDF p. 9, entropy-balance

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

/-- Entropy balance, §3.2, PDF p.9: extended entropy, nonnegative mean,
transport under time reversal, and all nonzero-time identities. -/
theorem entropy_balance (D : NonsingularSystem K M) :
    (∀ t, signedEntropy (pushedReference D t) (D.omega : Measure M) =
      -QAlgorithms.Papers.Independent.Next46.P01.extendedExpectation (D.omega : Measure M) (entropyCocycle D t)) ∧
    (∀ t, timeValue K t ≠ 0 →
      signedEntropy (pushedReference D t) (D.omega : Measure M) =
        -((timeValue K t : ℝ) : EReal) *
          QAlgorithms.Papers.Independent.Next46.P01.extendedExpectation (D.omega : Measure M) (meanEntropy D t)) ∧
    (∀ t, 0 < timeValue K t →
      0 ≤ QAlgorithms.Papers.Independent.Next46.P01.extendedExpectation (D.omega : Measure M) (meanEntropy D t)) ∧
    (∀ t, timeValue K t ≠ 0 → ∀ᵐ x ∂(D.omega : Measure M),
      meanEntropy D t x = meanEntropy D (-t) (D.flow t x)) ∧
    (∀ theta : M ≃ᵐ M, IsTimeReversal D theta →
      ∀ t, timeValue K t ≠ 0 → ∀ᵐ x ∂(D.omega : Measure M),
        meanEntropy D t (theta x) = -meanEntropy D (-t) x ∧
        meanEntropy D t (theta x) = -meanEntropy D t (D.flow (-t) x)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P03

end
