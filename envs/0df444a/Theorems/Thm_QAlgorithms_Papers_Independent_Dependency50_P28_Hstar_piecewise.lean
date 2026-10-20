-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_Hstar_piecewise
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.Hstar_piecewise
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:02:22.518276+00:00
-- url     : https://prove2.me/theorems/5fd471f0-3507-4e93-879a-7c3cfe3b4837
-- title:
--   Both rate branches and the unique crossing parameter
-- statement:
--   For distinct density operators with nested supports, put amax=Dmax(ρ‖σ) and rmax=φ(amax)+amax, and fix r≥0. When r<rmax there is a unique real aᵣ solving r−aᵣ=φ(aᵣ). The converse Hoeffding divergence satisfies
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
--   H_r^*(\rho\Vert\sigma)=\begin{cases}r-a_r=\varphi(a_r),&r<r_{\max},\\r-D_{\max}(\rho\Vert\sigma),&r\geq r_{\max}.\end{cases}
--   $$
--
--   The two branches describe the trade-off below and above the maximal crossing rate.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 15, Lemma IV.9

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

/-- arXiv:1309.3228v5, PDF p.15: Both rate branches and the unique crossing parameter. No interior premise is put on a_r. In particular a_r=r when r≤D. Equality r=rmax belongs to the second branch. The actual lemma starts on PDF p.15. -/
theorem Hstar_piecewise (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportLE rho sigma) (hne : rho ≠ sigma) (r : ℝ) (hr : 0 ≤ r) :
    ((r : EReal) < rmax rho sigma →
      ∃ a : ℝ, (r : EReal) - (a : EReal) = phi rho sigma a ∧
        Hstar rho sigma r = (r : EReal) - (a : EReal) ∧
        ∀ b : ℝ, (r : EReal) - (b : EReal) = phi rho sigma b → b = a) ∧
    (rmax rho sigma ≤ (r : EReal) →
      Hstar rho sigma r = (r : EReal) - Dmax rho sigma) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
