-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P03_lemma_5_4
-- name    : QAlgorithms.Papers.Independent.Support21.P03.lemma_5_4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:37:47.726703+00:00
-- url     : https://prove2.me/theorems/e0b616d6-8b21-432b-856a-b3b5917cb155
-- title:
--   Almost-sure forward and backward sign bounds
-- statement:
--   Let $(M,\mathcal F,\omega)$ be a probability space and let $\phi^t$ be a group of measurable automorphisms, jointly measurable in time and configuration, with time domain $\mathbb Z$ or $\mathbb R$. Assume that $\omega_t=(\phi^t)_*\omega$ is equivalent to $\omega$ for every time. Set $\ell_t=\log(d\omega_t/d\omega)$ and $c^t=\ell_t\circ\phi^t$. Equalities of observables are modulo $\omega$-null sets. Write $e_t(\alpha)=\log\int e^{\alpha\ell_t}\,d\omega$, retaining extended moment values. A time reversal $\vartheta$ is a measurable involution with $\vartheta\phi^t=\phi^{-t}\vartheta$ and $\vartheta_*\omega=\omega$.
--
--   In continuous time assume (E1): the actual RN densities form a strongly $C^1$ curve in $L^1(\omega)$, and their derivative $\sigma$ at zero has a strongly continuous transported orbit $\sigma_s=\sigma\circ\phi^s$ in $L^1(\omega)$. Write $A_t(x)=\int_0^t\sigma_s(x)\,ds$ and $m_t=t^{-1}\int_0^t\omega(\sigma_s)\,ds$ for $t\ne0$. Assume also (E2), $\sigma\in L^\infty(\omega)$. Let $m\in\mathbb R$ be the finite limit $m=\lim_{t\to\infty}m_t$ required by (E3).
--
--   A regular sequence is a nondecreasing sequence $t_n\to+\infty$ satisfying $\sum_n e^{-a t_n}<\infty$ for every $a>0$. For every such sequence, almost surely,
--   $$\liminf_{n\to\infty}\frac1{t_n}\int_0^{t_n}\sigma_s\,ds\ge0,\qquad
--   \limsup_{n\to\infty}\frac1{t_n}\int_0^{t_n}\sigma_{-s}\,ds\le0.$$
--
--   Both bounds hold on one conull set for the chosen sequence. Initial zero times have no effect on either limiting assertion.
-- source:
--   Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, PDF p. 25, Lemma 5.4

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

/-- Lemma 5.4, PDF p.25. Both inequalities hold on the same conull set;
liminf and limsup are extended real to avoid unbounded-sequence defaults. -/
theorem lemma_5_4 (D : RegularSystem M)
    (hE2 : MemLp (continuousSigma D) ∞ (D.omega : Measure M))
    (mean : ℝ) (hE3 : Tendsto (scalarMean D) atTop (𝓝 mean))
    (tn : ℕ → ℝ) (hregular : RegularSequence tn) :
    ∀ᵐ x ∂(D.omega : Measure M),
      0 ≤ Filter.liminf (fun n => (pointMean D (tn n) x : EReal)) atTop ∧
      Filter.limsup (fun n => (backwardPointMean D (tn n) x : EReal)) atTop ≤ 0 := by sorry

end QAlgorithms.Papers.Independent.Support21.P03

end
