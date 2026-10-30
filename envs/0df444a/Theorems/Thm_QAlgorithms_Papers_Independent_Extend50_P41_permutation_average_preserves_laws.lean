-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_permutation_average_preserves_laws
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.permutation_average_preserves_laws
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:47:48.733993+00:00
-- url     : https://prove2.me/theorems/28596f0f-292f-400c-8a99-34c8750c7c47
-- title:
--   Equations (79)–(80): symmetrization preserves every Born law
-- statement:
--   Let $d\ge1$, let $\mathcal S$ be the positive semidefinite trace-one matrices on $\mathbb C^d$, including singular matrices, and give $\mathcal S$ its usual matrix topology and Borel sets. Copy counts are positive. A scheme consists of normalized countably additive positive operator measures $E_N$ on $(\mathbb C^d)^{\otimes N}$, fixed independently of the unknown input. Its Born law is $\mu_{N,\rho}(B)=\operatorname{Tr}(\rho^{\otimes N}E_N(B))$. All logarithms are natural.
--
--   For every full scheme define the permutation average by
--   $$E_N^{\rm sym}(B)=\frac1{N!}\sum_{\pi\in S_N}V_\pi E_N(B)V_\pi^*.$$
--   It is a normalized permutation-invariant scheme, and for every $N$ and input $\rho$,
--   $$\mu_{N,\rho}^{\rm sym}=\mu_{N,\rho}.$$
--   Thus this finite-copy averaging preserves every Born law and consequently any LDP rate. No LDP premise is needed for the identity.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 17, Equations (79)-(80)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.17, (79)-(80): permutation averaging preserves every Born law,
hence any LDP rate, exactly at each finite N. No LDP premise is necessary. -/
theorem permutation_average_preserves_laws {d : ℕ} (hd : 0 < d)
    (E : Scheme d (DensityOutcome d)) :
    ∃ A : Scheme d (DensityOutcome d),
      (∀ k B, MeasurableSet B → (A.observable k).operator B = permutationAverageOperator E k B) ∧
      (∀ k, PermutationInvariantAt (A.observable k)) ∧
      ∀ k rho, A.law k rho = E.law k rho := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
