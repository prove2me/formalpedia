-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P34_pure_tripartite_entropy_balances
-- name    : QAlgorithms.Papers.Independent.Renew46.P34.pure_tripartite_entropy_balances
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:08:13.22764+00:00
-- url     : https://prove2.me/theorems/fa28014f-074b-4275-a8ab-e28beb630f67
-- title:
--   Pure-tripartite entropy identities and balances
-- statement:
--   Let $|\psi\rangle^{ABE}$ be a unit vector on finite nonzero registers, and let $\rho^{AB}=\operatorname{Tr}_E|\psi\rangle\langle\psi|$. All entropies are in bits and are evaluated on this same state. Write $I(A;B)=H(A)+H(B)-H(AB)$, $I(A;E)=H(A)+H(E)-H(AE)$ and $I_c(A\rangle B)=H(B)-H(AB)$.
--
--   Purity gives both marginal identities and both information balances:
--
--   $$H(AB)=H(E),\quad H(AE)=H(B),\qquad \frac{I(A;B)+I(A;E)}2=H(A),\quad \frac{I(A;B)-I(A;E)}2=I_c(A\rangle B).$$
--
--   These identities determine the rates of the child protocols; they require no communication-cost assumption.
-- source:
--   A family of quantum protocols, arXiv:quant-ph/0308044v2, PDF p. 1, Pure-tripartite entropy balances (two unnumbered displays)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P34

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P34

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.1, two unnumbered entropy balances, with both stated purity identities. -/
theorem pure_tripartite_entropy_balances {A B E : Type}
    [Fintype A] [Fintype B] [Fintype E] [Nonempty A] [Nonempty B] [Nonempty E]
    (psi : EuclideanSpace ℂ ((A × B) × E)) (hpsi : IsState psi) :
    vnEntropy (sourceAB psi) = vnEntropy (traceLeft (pureDensity psi)) ∧
    vnEntropy (sourceAE psi) = vnEntropy (traceLeft (sourceAB psi)) ∧
    informationAB psi / 2 + informationAE psi / 2 = entropyA psi ∧
    informationAB psi / 2 - informationAE psi / 2 = (vnEntropy (traceLeft (sourceAB psi)) - vnEntropy (sourceAB psi)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P34

end
