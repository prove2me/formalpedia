-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_single_shot_half_and_infinity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.single_shot_half_and_infinity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:09:09.04785+00:00
-- url     : https://prove2.me/theorems/0f55db12-8a49-4585-99c2-27f03bace12d
-- title:
--   Exact measurement attainment at one-half and infinity
-- statement:
--   For every pair of density operators in every finite dimension, there is a finite measurement attaining the new order-one-half divergence exactly, and there is a finite measurement attaining the infinite-order divergence exactly. The infinite-order new divergence is Dmax, namely
--
--   Write $Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $F_\alpha=\log Q_\alpha$. Powers are evaluated only on positive eigenvalues and are zero on the kernel, even at exponent zero; scalar logarithms satisfy $\log0=-\infty$.
--
--   The normalized new divergence is $\widetilde D_\alpha=(F_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ when the supports are nested or $0<\alpha<1$, and is $+\infty$ otherwise; the first argument has positive trace. For states the trace-normalizing term is zero.
--
--   Here $D(\rho\Vert\sigma)=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]/\operatorname{Tr}\rho$ on nested supports and $+\infty$ otherwise, and $D_{\max}(\rho\Vert\sigma)=\inf\{a\in\mathbb R:\rho\leq e^a\sigma\}$, with the empty infimum equal to $+\infty$. All operator inequalities are in Loewner order.
--
--   $D_{\max}$ is also the infinite-order new divergence, and $\widetilde D_{1/2}=-2\log F$ for the unsquared Uhlmann root fidelity $F$. Exact attainment refers to a finite measurement, with arbitrary outcome cardinality.
--
--   $$
--   \widetilde D_{1/2}(M(\rho)\Vert M(\sigma))=\widetilde D_{1/2}(\rho\Vert\sigma),\qquad D_{\max}(N(\rho)\Vert N(\sigma))=D_{\max}(\rho\Vert\sigma),\qquad\lim_{\alpha\to\infty}\widetilde D_\alpha=D_{\max}.
--   $$
--
--   These are exact finite-measurement attainment statements at two distinguished orders.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 24, Lemma A.4 D1/2           and D+∞ = Dmax satisfy AM.

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P28

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:1309.3228v5, PDF p.24: Exact measurement attainment at one-half and infinity. The two measurements need not coincide. Dnew at one-half uses −2 log(root fidelity). Infinity identification is the limit stated in (47), p.10. -/
theorem single_shot_half_and_infinity  :
    AM (newFamily (1 / 2)) ∧ AM maxFamily ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I], ∀ rho sigma : Mat I,
      IsDensityMatrix rho → IsDensityMatrix sigma →
      Tendsto (fun alpha : ℝ => Dnew alpha rho sigma) atTop (nhds (Dmax rho sigma))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
