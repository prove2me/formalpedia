-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P63_eq20_equivalentEqualities
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P63.eq20_equivalentEqualities
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:41:29.003861+00:00
-- url     : https://prove2.me/theorems/c6420882-a636-478c-b81b-f2ddf41fa860
-- title:
--   Equation (20): equivalence of the endpoint-exchanged SSA equalities
-- statement:
--   All states below are positive trace-class density operators of trace one on completed complex Hilbert tensor products, represented in countable orthonormal coordinates. Finite dimensional systems are included. Entropies use natural logarithms and the convention $0\log 0=0$. Every subsystem entropy occurring in an entropy difference is finite; this is the proof-supported finite-entropy reading of the source, and imposes no finite Hilbert dimension.
--
--   For every tripartite state $\rho$, with $I(A:B)=S_A+S_B-S_{A\cup B}$ formed from its actual marginals,
--
--   $$I(1:2)_\rho=I(1:23)_\rho\quad\Longleftrightarrow\quad I(2:3)_\rho=I(12:3)_\rho.$$
--
--   Thus SSA equality in one endpoint orientation is equivalent to equality in the other. This is a general entropy identity; the biorthogonal family is an application.
-- source:
--   On Mutual Information in Multipartite Quantum States and Equality in Strong Subadditivity of Entropy, arXiv:quant-ph/0311193v1, PDF p. 8, Unnumbered Eq. (20): equivalent SSA equality after exchanging the endpoint roles

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P63

noncomputable section

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted nuclear trace-class, positive, trace-one predicate verbatim.

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (finiteRelativeEntropy)

/-- Unnumbered (20), PDF p.8: the endpoint-exchanged SSA equalities are equivalent
for every finite-entropy tripartite density, without an ensemble premise. -/
theorem eq20_equivalentEqualities (rho : (Matrix (Fin 3 → ℕ) (Fin 3 → ℕ) ℂ)) (hrho : IsDensity rho)
    (hfinite : FiniteSubsystemEntropies rho) :
    clusterMutualInformation rho {0} {1} = clusterMutualInformation rho {0} {1, 2} ↔
      clusterMutualInformation rho {1} {2} = clusterMutualInformation rho {0, 1} {2} := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P63

end
