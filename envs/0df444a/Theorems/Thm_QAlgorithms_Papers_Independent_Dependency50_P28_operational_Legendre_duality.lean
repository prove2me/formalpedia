-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_operational_Legendre_duality
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.operational_Legendre_duality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:04:28.343855+00:00
-- url     : https://prove2.me/theorems/8a8f4291-246a-4728-ad1a-530c349eace4
-- title:
--   Forward and inverse operational Legendre representations
-- statement:
--   For distinct density operators with nested supports, let ψ̃(u)=(1−u)ψ(u/(1−u)), 0≤u<1. This function is continuous and convex, and B*ₑ(r)=H*ᵣ=sup_{0≤u<1}{ru−ψ̃(u)} for r≥0. For every α>1, set u=(α−1)/α. The inverse operational representation is
--
--   Write $Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $F_\alpha=\log Q_\alpha$. Powers are evaluated only on positive eigenvalues and are zero on the kernel, even at exponent zero; scalar logarithms satisfy $\log0=-\infty$.
--
--   The normalized new divergence is $\widetilde D_\alpha=(F_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ when the supports are nested or $0<\alpha<1$, and is $+\infty$ otherwise; the first argument has positive trace. For states the trace-normalizing term is zero.
--
--   Here $D(\rho\Vert\sigma)=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]/\operatorname{Tr}\rho$ on nested supports and $+\infty$ otherwise, and $D_{\max}(\rho\Vert\sigma)=\inf\{a\in\mathbb R:\rho\leq e^a\sigma\}$, with the empty infimum equal to $+\infty$. All operator inequalities are in Loewner order.
--
--   The rate transforms are $\psi(s)=F_{1+s}(\rho\Vert\sigma)$, $\varphi(a)=\sup_{s\geq0}\{as-\psi(s)\}$, and $\widetilde\psi(u)=(1-u)\psi(u/(1-u))$ for $0\leq u<1$.
--
--   Write $H_r^*=\sup_{\alpha>1}\frac{\alpha-1}{\alpha}[r-\widetilde D_\alpha]$. For tests $0\leq T_n\leq I$ on $n$ copies, success is $\operatorname{Tr}\rho^{\otimes n}T_n$ and type-II error is $\beta_n=\operatorname{Tr}\sigma^{\otimes n}T_n$. The operational exponent is $B_e^*(r)=\inf_{(T_n):\,\limsup_n n^{-1}\log\beta_n\leq-r}\{-\liminf_n n^{-1}\log\operatorname{Tr}\rho^{\otimes n}T_n\}$.
--
--   $$
--   \sup_{r\geq0}\{ur-B_e^*(r)\}=\widetilde\psi(u)=\frac{\alpha-1}{\alpha}\widetilde D_\alpha(\rho\Vert\sigma).
--   $$
--
--   This recovers the quantum Renyi divergences from the operational testing exponents.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 17, Remark IV.13 By Theorem IV.10 and (78), we have

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

/-- arXiv:1309.3228v5, PDF p.17: Forward and inverse operational Legendre representations. Extended suprema prevent boundedness defaults. The displayed inverse formula excludes u=0 through alpha>1. -/
theorem operational_Legendre_duality (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportLE rho sigma) (hne : rho ≠ sigma) :
    ContinuousOn (psiTilde rho sigma) (Set.Ico 0 1) ∧
    ConvexOn ℝ (Set.Ico 0 1) (psiTilde rho sigma) ∧
    (∀ r : ℝ, 0 ≤ r → strongExponent rho sigma r = Hstar rho sigma r ∧
      Hstar rho sigma r = sSup {v | ∃ u : ℝ, 0 ≤ u ∧ u < 1 ∧
        v = ((r * u - psiTilde rho sigma u : ℝ) : EReal)}) ∧
    (∀ alpha : ℝ, 1 < alpha →
      let u : ℝ := (alpha - 1) / alpha
      sSup {v | ∃ r : ℝ, 0 ≤ r ∧
        v = ((u * r : ℝ) : EReal) - strongExponent rho sigma r} =
        (psiTilde rho sigma u : EReal) ∧
      (psiTilde rho sigma u : EReal) = (((alpha - 1) / alpha : ℝ) : EReal) * Dnew alpha rho sigma) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
