-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P26_spectral_permutation_bounds
-- name    : QAlgorithms.Papers.Independent.Claimed50.P26.spectral_permutation_bounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:08:17.225573+00:00
-- url     : https://prove2.me/theorems/371554bc-bef7-4547-a64e-99ba6b2f0923
-- title:
--   Lemma IV.11 (uniform spectral permutation trace bounds)
-- statement:
--   Let $A,B$ be positive semidefinite complex $d\times d$ matrices. Let $(\lambda_j^A)_{j=1}^d$ and $(\lambda_j^B)_{j=1}^d$ list their eigenvalues with multiplicity in any fixed order. There are permutations $\pi_{\min},\pi_{\max}\in S_d$, depending on those matrices and lists, such that every unitary $U$ satisfies
--
--   $$
--   \sum_{j=1}^d\lambda^A_{\pi_{\min}(j)}\lambda^B_j
--   \le\operatorname{Re}\operatorname{Tr}(UAU^\dagger B)
--   \le\sum_{j=1}^d\lambda^A_{\pi_{\max}(j)}\lambda^B_j.
--   $$
--
--   No trace normalization is required. The trace is real for these Hermitian factors; its real part is used explicitly. Empty dimension gives zero throughout, and scalar dimension gives equality. The permutations bound the trace uniformly over all unitary conjugations.
-- source:
--   A strong converse for classical channel coding using entangled inputs, arXiv:0903.2838v1, PDF p. 9, Lemma IV.11 (uniform spectral permutation trace bounds)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P26

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate Topology

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P26

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage depolarizing)

open QAlgorithms.Papers.Independent.Information100.P71
  (supportPower channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P23
  (UACode uaCodeSuccess uaSuccess ordinaryClassicalCapacity)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (renyiEntropy petz relative)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

/-- PDF p.9, Lemma IV.11: permutations depend on both full eigenvalue lists,
chosen before every unitary; PSD operators need not have trace one. -/
theorem spectral_permutation_bounds {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (lambdaA lambdaB : Fin d → ℝ)
    (hEA : HasEigenvalues A lambdaA) (hEB : HasEigenvalues B lambdaB) :
    ∃ piMin piMax : Equiv.Perm (Fin d), ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      (∑ j, lambdaA (piMin j)*lambdaB j) ≤
        (((U : Matrix (Fin d) (Fin d) ℂ)*A*(U : Matrix (Fin d) (Fin d) ℂ)ᴴ*B).trace.re) ∧
      (((U : Matrix (Fin d) (Fin d) ℂ)*A*(U : Matrix (Fin d) (Fin d) ℂ)ᴴ*B).trace.re) ≤
        ∑ j, lambdaA (piMax j)*lambdaB j := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P26

end
