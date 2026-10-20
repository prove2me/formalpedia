-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_D_CPTP_monotone
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.D_CPTP_monotone
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:52:54.072867+00:00
-- url     : https://prove2.me/theorems/d6f6fe0a-5313-4a2d-96f1-9570a0478180
-- title:
--   CPTP monotonicity of the new divergences and relative entropy
-- statement:
--   Let ρ,σ≥0 with Tr ρ>0 and let Φ be CPTP, with arbitrary finite input and output dimensions. The normalized new divergence is monotone for every α>1; the α↓1 limit yields the same inequality for normalized Umegaki relative entropy D:
--
--   Write $Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $F_\alpha=\log Q_\alpha$. Powers are evaluated only on positive eigenvalues and are zero on the kernel, even at exponent zero; scalar logarithms satisfy $\log0=-\infty$.
--
--   The normalized new divergence is $\widetilde D_\alpha=(F_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ when the supports are nested or $0<\alpha<1$, and is $+\infty$ otherwise; the first argument has positive trace. For states the trace-normalizing term is zero.
--
--   Here $D(\rho\Vert\sigma)=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]/\operatorname{Tr}\rho$ on nested supports and $+\infty$ otherwise, and $D_{\max}(\rho\Vert\sigma)=\inf\{a\in\mathbb R:\rho\leq e^a\sigma\}$, with the empty infimum equal to $+\infty$. All operator inequalities are in Loewner order.
--
--   $$
--   \widetilde D_\alpha(\Phi(\rho)\Vert\Phi(\sigma))\leq\widetilde D_\alpha(\rho\Vert\sigma),\qquad D(\Phi(\rho)\Vert\Phi(\sigma))\leq D(\rho\Vert\sigma).
--   $$
--
--   The two inequalities express data processing for finite orders and their relative-entropy limit.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 7, Corollary III.14 The new Rényi relative entropies are monotone under CPTP maps for α > 1. That

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

/-- arXiv:1309.3228v5, PDF p.7: CPTP monotonicity of the new divergences and relative entropy. Both conclusions are retained. No support inclusion is added. -/
theorem D_CPTP_monotone (rho sigma : Mat I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef) (htrace : 0 < tr rho) (Phi : Mat I →ₗ[ℂ] Mat J) (hPhi : CPTP Phi) :
    (∀ alpha : ℝ, 1 < alpha → Dnew alpha (Phi rho) (Phi sigma) ≤ Dnew alpha rho sigma) ∧
    relativeEntropy (Phi rho) (Phi sigma) ≤ relativeEntropy rho sigma := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
