-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P03_proposition_3_4
-- name    : QAlgorithms.Papers.Independent.Support21.P03.proposition_3_4
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:32:24.56899+00:00
-- url     : https://prove2.me/theorems/a02aca28-55ce-4a8f-b42e-b4831ee505eb
-- title:
--   Convexity, bounds and analyticity of the finite entropy functional
-- statement:
--   Let $(M,\mathcal F,\omega)$ be a probability space and let $\phi^t$ be a group of measurable automorphisms, jointly measurable in time and configuration, with time domain $\mathbb Z$ or $\mathbb R$. Assume that $\omega_t=(\phi^t)_*\omega$ is equivalent to $\omega$ for every time. Set $\ell_t=\log(d\omega_t/d\omega)$ and $c^t=\ell_t\circ\phi^t$. Equalities of observables are modulo $\omega$-null sets. Write $e_t(\alpha)=\log\int e^{\alpha\ell_t}\,d\omega$, retaining extended moment values. A time reversal $\vartheta$ is a measurable involution with $\vartheta\phi^t=\phi^{-t}\vartheta$ and $\vartheta_*\omega=\omega$.
--
--   Write $e_t(\alpha)=\log\int_M e^{\alpha\ell_t}\,d\omega$ as an extended logarithmic moment, and $\operatorname{Ent}(\nu\mid\mu)=-D_{\rm KL}(\nu\Vert\mu)$. For every time $t$, the function $e_t:\mathbb R\to(-\infty,+\infty]$ is convex, $e_t(0)=e_t(1)=0$, is nonpositive on $[0,1]$ and nonnegative outside it. Moreover,
--   $$e_t(\alpha)\ge\min\{\alpha\operatorname{Ent}(\omega\mid\omega_t),(1-\alpha)\operatorname{Ent}(\omega_t\mid\omega)\},$$
--   and $e_t$ is real analytic on $(0,1)$.
--
--   The entropy bound retains infinite entropy and uses $0\cdot(\pm\infty)=0$ at the endpoints.
-- source:
--   Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, PDF p. 10, Proposition 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

/-- Proposition 3.4, PDF p.10: all three clauses, including the minimum
of the two signed-entropy bounds and real analyticity on the open unit interval. -/
theorem proposition_3_4 (D : NonsingularSystem K M) (t : K.Carrier) :
    ExtendedConvex (finiteES D t) ∧
    finiteES D t 0 = 0 ∧ finiteES D t 1 = 0 ∧
    (∀ alpha, (⊥ : EReal) < finiteES D t alpha) ∧
    (∀ alpha ∈ Icc (0 : ℝ) 1, finiteES D t alpha ≤ 0) ∧
    (∀ alpha, alpha ∉ Icc (0 : ℝ) 1 → 0 ≤ finiteES D t alpha) ∧
    (∀ alpha : ℝ, min ((alpha : EReal) * signedEntropy (D.omega : Measure M) (pushedReference D t))
      (((1 - alpha : ℝ) : EReal) * signedEntropy (pushedReference D t) (D.omega : Measure M))
        ≤ finiteES D t alpha) ∧
    AnalyticOnNhd ℝ (fun alpha => (finiteES D t alpha).toReal) (Ioo (0 : ℝ) 1) := by sorry

end QAlgorithms.Papers.Independent.Support21.P03

end
