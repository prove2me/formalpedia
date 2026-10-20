-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_D_order_monotone
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.D_order_monotone
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:51:26.477179+00:00
-- url     : https://prove2.me/theorems/3af93e38-5321-404b-a1bd-f6a4a3a8acd2
-- title:
--   The new divergence increases with its order
-- statement:
--   Fix ρ,σ≥0 with Tr ρ>0. The normalized sandwiched divergences, taking value +∞ on support failure, increase with their order:
--
--   Write $Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $F_\alpha=\log Q_\alpha$. Powers are evaluated only on positive eigenvalues and are zero on the kernel, even at exponent zero; scalar logarithms satisfy $\log0=-\infty$.
--
--   The normalized new divergence is $\widetilde D_\alpha=(F_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ when the supports are nested or $0<\alpha<1$, and is $+\infty$ otherwise; the first argument has positive trace. For states the trace-normalizing term is zero.
--
--   $$
--   1<\alpha\leq\beta\quad\Longrightarrow\quad\widetilde D_\alpha(\rho\Vert\sigma)\leq\widetilde D_\beta(\rho\Vert\sigma).
--   $$
--
--   This orders the normalized sandwiched divergences by their Renyi parameter.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 7, Corollary III.12

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

/-- arXiv:1309.3228v5, PDF p.7: The new divergence increases with its order. -/
theorem D_order_monotone (rho sigma : Mat I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef) (htrace : 0 < tr rho) :
    MonotoneOn (fun alpha : ℝ => Dnew alpha rho sigma) (Set.Ioi 1) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
