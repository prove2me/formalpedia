-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P63_eq19_pairedExcesses
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P63.eq19_pairedExcesses
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:40:32.174087+00:00
-- url     : https://prove2.me/theorems/c6a90444-1398-4e72-9d49-91a42b205ebb
-- title:
--   Equation (19): the six directed SSA excesses agree in three pairs
-- statement:
--   All states below are positive trace-class density operators of trace one on completed complex Hilbert tensor products, represented in countable orthonormal coordinates. Finite dimensional systems are included. Entropies use natural logarithms and the convention $0\log 0=0$. Every subsystem entropy occurring in an entropy difference is finite; this is the proof-supported finite-entropy reading of the source, and imposes no finite Hilbert dimension.
--
--   Let $\rho$ be any tripartite state, and let $(a,b,c)$ be any permutation of its three parties. Write $I(A:B)=S_A+S_B-S_{A\cup B}$ for mutual information of disjoint clusters. Then
--
--   $$I(a:bc)_\rho-I(a:b)_\rho=I(ab:c)_\rho-I(b:c)_\rho.$$
--
--   This pairs the six directed SSA excesses into three equal pairs. Each displayed side expands to $S_{ab}+S_{bc}-S_b-S_{abc}$; the statement does not equate all six excesses.
-- source:
--   On Mutual Information in Multipartite Quantum States and Equality in Strong Subadditivity of Entropy, arXiv:quant-ph/0311193v1, PDF p. 8, Unnumbered Eq. (19): pairwise equality of the six SSA excesses

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P63

noncomputable section

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted nuclear trace-class, positive, trace-one predicate verbatim.

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (finiteRelativeEntropy)

/-- Unnumbered (19), PDF pp.7–8: the six directed SSA excesses pair up under party
permutations. This states every permutation; it does not equate all six excesses. -/
theorem eq19_pairedExcesses (rho : (Matrix (Fin 3 → ℕ) (Fin 3 → ℕ) ℂ)) (hrho : IsDensity rho)
    (hfinite : FiniteSubsystemEntropies rho) (p : Equiv.Perm (Fin 3)) :
    clusterMutualInformation rho {p 0} {p 1, p 2} - clusterMutualInformation rho {p 0} {p 1} =
      clusterMutualInformation rho {p 0, p 1} {p 2} - clusterMutualInformation rho {p 1} {p 2} := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P63

end
