-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_asymptotic_D_attainment
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.asymptotic_D_attainment
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:49:38.67787+00:00
-- url     : https://prove2.me/theorems/14ffc4a3-61fb-45ea-95b2-98566713d731
-- title:
--   Asymptotic pinching and maximum-measurement attainment of the new divergence
-- statement:
--   Let ρ,σ≥0 with Tr ρ>0, and let α>1. Put ρₙ=ρ^{⊗n}, σₙ=σ^{⊗n}, and let ρ̂ₙ be the pinching of ρₙ by σₙ, and let D̃α be the sandwiched divergence normalized by Tr ρ as in (6). For each n≥1 the measurement maximum is attained over all finite POVMs. Without a support-inclusion assumption,
--
--   Write $Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $F_\alpha=\log Q_\alpha$. Powers are evaluated only on positive eigenvalues and are zero on the kernel, even at exponent zero; scalar logarithms satisfy $\log0=-\infty$.
--
--   The normalized new divergence is $\widetilde D_\alpha=(F_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ when the supports are nested or $0<\alpha<1$, and is $+\infty$ otherwise; the first argument has positive trace. For states the trace-normalizing term is zero.
--
--   $$
--   \widetilde D_\alpha(\rho\Vert\sigma)=\lim_n\frac1n\widetilde D_\alpha(\widehat\rho_n\Vert\sigma_n)=\lim_n\frac1n\max_M\widetilde D_\alpha(M(\rho_n)\Vert M(\sigma_n)).
--   $$
--
--   The result supplies the corresponding regularized measurement interpretation of the normalized divergence, including support failure.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 6, Corollary III.8

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

/-- arXiv:1309.3228v5, PDF p.6: Asymptotic pinching and maximum-measurement attainment of the new divergence. Tr rho>0 is the implicit normalization domain. Support failure and sigma=0 remain allowed and give +infinity. -/
theorem asymptotic_D_attainment (rho sigma : Mat I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef) (htrace : 0 < tr rho) (alpha : ℝ) (ha : 1 < alpha) :
    (∀ n : ℕ, 1 ≤ n → ∃ M : POVM (Fin n → I),
      measuredD alpha (copies n rho) (copies n sigma) M =
        maxMeasuredD alpha (copies n rho) (copies n sigma)) ∧
    Tendsto (fun n => scaled n (Dnew alpha
      (pinch (copies (n + 1) sigma) (copies (n + 1) rho)) (copies (n + 1) sigma)))
      atTop (nhds (Dnew alpha rho sigma)) ∧
    Tendsto (fun n => scaled n (maxMeasuredD alpha (copies (n + 1) rho) (copies (n + 1) sigma)))
      atTop (nhds (Dnew alpha rho sigma)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
