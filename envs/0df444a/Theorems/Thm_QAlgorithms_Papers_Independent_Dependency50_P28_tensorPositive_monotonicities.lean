-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_tensorPositive_monotonicities
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.tensorPositive_monotonicities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:55:32.986403+00:00
-- url     : https://prove2.me/theorems/c4724f7e-6b9d-4605-8a44-a1c50f14b71b
-- title:
--   Monotonicity under tensor-stable positive maps
-- statement:
--   Let Φ be complex-linear and trace preserving, and suppose every positive tensor power Φ^{⊗n} is positive on all positive operators. The monotonicity conclusions of III.13–III.15 hold: Fα and Qα decrease for PSD pairs with nested supports and α>1; for Tr ρ>0, normalized new divergences and their Umegaki limit decrease even without nested supports:
--
--   Write $Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $F_\alpha=\log Q_\alpha$. Powers are evaluated only on positive eigenvalues and are zero on the kernel, even at exponent zero; scalar logarithms satisfy $\log0=-\infty$.
--
--   The normalized new divergence is $\widetilde D_\alpha=(F_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ when the supports are nested or $0<\alpha<1$, and is $+\infty$ otherwise; the first argument has positive trace. For states the trace-normalizing term is zero.
--
--   Here $D(\rho\Vert\sigma)=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]/\operatorname{Tr}\rho$ on nested supports and $+\infty$ otherwise, and $D_{\max}(\rho\Vert\sigma)=\inf\{a\in\mathbb R:\rho\leq e^a\sigma\}$, with the empty infimum equal to $+\infty$. All operator inequalities are in Loewner order.
--
--   $$
--   F_\alpha(\Phi\rho\Vert\Phi\sigma)\leq F_\alpha(\rho\Vert\sigma),\quad Q_\alpha(\Phi\rho\Vert\Phi\sigma)\leq Q_\alpha(\rho\Vert\sigma),\quad\widetilde D_\alpha(\Phi\rho\Vert\Phi\sigma)\leq\widetilde D_\alpha(\rho\Vert\sigma).
--   $$
--
--   This identifies the weaker tensor-positive map hypothesis sufficient for the three monotonicity statements.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 8, Remark III.18 Note that the monotonicity properties in Corollaries III.13, III.14 and III.15 hold for

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

/-- arXiv:1309.3228v5, PDF p.8: Monotonicity under tensor-stable positive maps. The hypotheses for each of the three referenced corollaries are preserved separately, including the relative-entropy clause of III.14. -/
theorem tensorPositive_monotonicities (rho sigma : Mat I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef) (Phi : Mat I →ₗ[ℂ] Mat J)
    (htp : TP Phi) (hpos : TensorPositive Phi) :
    (SupportLE rho sigma → ∀ alpha : ℝ, 1 < alpha →
      F alpha (Phi rho) (Phi sigma) ≤ F alpha rho sigma ∧
      Q alpha (Phi rho) (Phi sigma) ≤ Q alpha rho sigma) ∧
    (0 < tr rho →
      (∀ alpha : ℝ, 1 < alpha → Dnew alpha (Phi rho) (Phi sigma) ≤ Dnew alpha rho sigma) ∧
      relativeEntropy (Phi rho) (Phi sigma) ≤ relativeEntropy rho sigma) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
