-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P60_depolarizing_constant
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P60.depolarizing_constant
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:54:46.17965+00:00
-- url     : https://prove2.me/theorems/4d79e677-5de4-4e7d-9fa4-c9fa7c5fa9f4
-- title:
--   Example 6: depolarizing dilation subspaces have constant formation and cost
-- statement:
--   Let $d\ge2$ and $-1/(d^2-1)\le\lambda\le1$. Choose unitaries $\sigma_0,\ldots,\sigma_{d^2-1}$ on $\mathbb C^d$ with $\sigma_0=I$ and $\operatorname{Tr}(\sigma_i^\dagger\sigma_j)=d\delta_{ij}$. Put $p_0=\lambda+(1-\lambda)/d^2$ and $p_i=(1-p_0)/(d^2-1)$ for $i>0$. Define the isometry
--   $$U_\lambda x=\sum_{i=0}^{d^2-1}\sqrt{p_i}\,\sigma_i x\otimes |i\rangle,$$
--   and its range $K_\lambda\subset\mathbb C^d\otimes\mathbb C^{d^2}$. Let $a=\lambda+(1-\lambda)/d$, $b=(1-\lambda)/d$, and $h_\lambda=-a\log_2 a-(d-1)b\log_2 b$, using $0\log_2 0=0$. This is the minimum output entropy of the depolarizing channel.
--
--   Every density matrix $\rho$ supported on $K_\lambda$ satisfies
--   $$E_c(\rho)=E_f(\rho)=h_\lambda.$$
--   For every positive integer $n$, every convex mixture of product states on $K_\lambda^{\otimes n}$ has formation $nh_\lambda$. The tensor cut groups all output systems against all environment systems. Product factors may be mixed supported density matrices. This family gives explicitly computable entanglement costs.
--
--   Here $E_f$ is the infimum of average pure-state marginal entropy over normalized finite decompositions of the stated density matrix. $E_c$ is the asymptotic EPR preparation rate under deterministic two-way LOCC, and $E_D$ is the corresponding asymptotic distillation rate, in bits per copy. All entropies and logarithms are in bits.
-- source:
--   Remarks on additivity of the Holevo channel capacity and of the entanglement of formation, arXiv:quant-ph/0206148v4, PDF p. 10, Example 6: depolarizing dilation subspaces have constant formation and cost

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P60

namespace QAlgorithms.Papers.Independent.Intakenext100.P60

open scoped Matrix ComplexConjugate ComplexOrder TensorProduct

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix, normalized ensemble, convex roof, grouped copies and LOCC.

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P08 (PureEnsemble pureAverage formation)

open QAlgorithms.Papers.Independent.Information100.P80 (groupedPower)

open QAlgorithms.Papers.Independent.Gap48.P32 (twoWayDistillable)

/-- PDF pp.10--11, Example 6: every supported state has the same cost and formation;
mixtures of n-fold product states have formation n times the same entropy. -/
theorem depolarizing_constant {d : ℕ} (D : DepolarizingData d) :
    (∀ rho : Op (Fin d × Fin (d ^ 2)), IsDensityMatrix rho →
      HasRangeIn (dilationSpace (depolarizingDilation D)) rho →
      formationCostBits rho = depolarizingEntropyBits D ∧ formation rho = depolarizingEntropyBits D) ∧
    (∀ n : ℕ, 0 < n → ∀ m : ℕ, ∀ mu : Fin m → ℝ,
      (∀ j, 0 ≤ mu j) → (∑ j, mu j) = 1 →
      ∀ rho : Fin m → Fin n → Op (Fin d × Fin (d ^ 2)),
      (∀ j i, IsDensityMatrix (rho j i)) →
      (∀ j i, HasRangeIn (dilationSpace (depolarizingDilation D)) (rho j i)) →
      formation (productMixture n m mu rho) = n * depolarizingEntropyBits D) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P60
