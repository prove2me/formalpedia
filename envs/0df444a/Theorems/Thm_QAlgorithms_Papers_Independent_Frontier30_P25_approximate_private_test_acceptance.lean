-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P25_approximate_private_test_acceptance
-- name    : QAlgorithms.Papers.Independent.Frontier30.P25.approximate_private_test_acceptance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:40:00.676386+00:00
-- url     : https://prove2.me/theorems/099bf309-32f4-4f48-af62-457bcf8f5e50
-- title:
--   Approximate private states pass their matching privacy test
-- statement:
--   Let $K,S,T$ be nonempty finite basis sets for the key alphabet and Alice and Bob's shield registers. Let $\theta_{ST}$ be a density operator and let $U=\sum_{i,j}|ij\rangle\langle ij|\otimes U_{ij}$, with every $U_{ij}$ unitary on $S\otimes T$. Define the private state $\gamma=U(\Phi_{KK}\otimes\theta)U^\dagger$ and its privacy effect $\Pi=U(\Phi_{KK}\otimes I_{ST})U^\dagger$, where $\Phi$ is the normalized maximally entangled projector. The physical party cut is $KS:KT$.
--
--   For every density operator $\rho$ on these same registers and every $0\le\varepsilon\le1$, squared fidelity $F(\rho,\gamma)\ge1-\varepsilon$ implies
--
--   $$\operatorname{Tr}(\Pi\rho)\ge1-\varepsilon.$$
--
--   The privacy test uses the same twisting as the approximated private state. This is the acceptance estimate used by the private meta-converse.
-- source:
--   Converse bounds for private communication over quantum channels, arXiv:1602.08898v3, PDF p. 16, Lemma 9

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P25

open scoped Matrix ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Pinned accepted definitions; assessments record the domains of equivalence.

open QAlgorithms.Papers.Independent.Dependency50.P09 (OneDesign relativeD sandwichedD)

open QAlgorithms.Papers.Independent.Dependency50.P24 (logBits idealCCQ)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity privateState privacyTest)

/-- PDF p.16, Lemma 9: the matching privacy test accepts an approximate private state.
The pinned private state and effect use tensor order K,S,K,T; the physical cut is KS:KT.
Only diagonal twisting blocks enter either matrix, so this covers every source twisting. -/
theorem approximate_private_test_acceptance
    {S T : Type*} [Fintype S] [Nonempty S] [Fintype T] [Nonempty T]
    (k : ℕ) (hk : 0 < k) (U : Fin k → Matrix.unitaryGroup (S × T) ℂ)
    (theta : Matrix (S × T) (S × T) ℂ) (htheta : IsDensityMatrix theta)
    (rho : Matrix (Fin k × (S × (Fin k × T))) (Fin k × (S × (Fin k × T))) ℂ)
    (hrho : IsDensityMatrix rho) (eps : ℝ) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hclose : 1 - eps ≤ squaredFidelity rho
      (privateState (fun i => (U i : Matrix (S × T) (S × T) ℂ)) theta)) :
    1 - eps ≤ effectProb
      (privacyTest (fun i => (U i : Matrix (S × T) (S × T) ℂ))) rho := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P25

end
