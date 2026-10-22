-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P39_classical_quantum_capacity
-- name    : QAlgorithms.Papers.Independent.Gap48.P39.classical_quantum_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:15:43.814625+00:00
-- url     : https://prove2.me/theorems/24579caf-eb41-4255-9c4d-351612bbdca2
-- title:
--   Theorem 3: general classical–quantum broadcast capacity
-- statement:
--   Let $\mathcal N:A'\to BC$ be any finite-dimensional CPTP broadcast channel on positive-dimensional systems. Define $CQ(\mathcal N)$ as the closed vanishing-error region for a common classical message of rate $R$ to both receivers and Alice–Bob entanglement of rate $Q$. Alice prepares a unit pure reference/input state for each message; Bob uses a local instrument and Charlie a local measurement. Every message must pass one squared-fidelity test to both correct labels tensor an EPR state of local rank $\lfloor2^{nQ}\rfloor$, with no shared resources or side communication. Let $\mathcal R(\mathcal N)$ contain nonnegative pairs satisfying, for a finite pure ensemble $\{p(t),\phi_t^{AA'}\}$,
--
--   $$Q\le I(A\rangle BT)_\sigma,\qquad R\le\min\{I(T;B)_\sigma,I(T;C)_\sigma\},\qquad \sigma=\bigoplus_t p(t)(\mathrm{id}_A\otimes\mathcal N)(\phi_t).$$
--
--   Then $\overline{\mathcal R(\mathcal N)}\subseteq CQ(\mathcal N)$; restricting the union to $|T|\le\min\{|A'|^2,|B|^2+|C|^2-1\}$ does not change it. Moreover,
--
--   $$CQ(\mathcal N)=\overline{\bigcup_{n\ge1}\frac1n\mathcal R(\mathcal N^{\otimes n})}.$$
--
--   All entropies use base two. Conditional coherent information is computed from the actual channel output and may have negative individual ensemble terms. This is the general regularized capacity characterization, with the one-letter state and boundary closure made explicit.
-- source:
--   Quantum broadcast channels, arXiv:quant-ph/0603098v2, PDF p. 7, Theorem 3: general classical–quantum broadcast capacity

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P39

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Gap48.P39

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Claimed50.P08 (cqBlocks holevoInfo)

open QAlgorithms.Papers.Independent.Dependency50.P19 (both epr mutualInformation marginalRA marginalRB)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity conditionalEntropy groupedChannelPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C X T E : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype X] [DecidableEq X]

variable [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E]

/-- Theorem 3, PDF pp.7–8,10,14. One-letter (24), both receiver constraints,
source cap, and equality with the CLOSED regularized union (no boundary attainment claim). -/
theorem classical_quantum_capacity [Nonempty A] [Nonempty B] [Nonempty C]
    (N : Superop A (B × C)) (hN : IsChannel N) :
    closure (quantumInformationRegion N false) ⊆ cqGenerationCapacity N ∧
    quantumInformationRegion N false = quantumInformationRegion N true ∧
    cqGenerationCapacity N = closure (regularizedQuantumRegion N) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P39

end
