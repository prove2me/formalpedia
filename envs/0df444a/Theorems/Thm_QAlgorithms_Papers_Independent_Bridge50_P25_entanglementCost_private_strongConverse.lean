-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P25_entanglementCost_private_strongConverse
-- name    : QAlgorithms.Papers.Independent.Bridge50.P25.entanglementCost_private_strongConverse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:02:50.4203+00:00
-- url     : https://prove2.me/theorems/1609a729-fc87-4147-9704-bbe2b8ceb8e8
-- title:
--   Theorem II.4: entanglement cost is a private strong-converse bound
-- statement:
--   Let $T:M_{d_A}\to M_{d_B}$ be a finite-dimensional quantum channel with positive dimensions. For a bipartite state, let $E_F$ be the infimum of the mean marginal entropy over its normalized pure-state decompositions, with entropy in bits. Define $E_F(T)$ by the supremum of output $E_F$ over all normalized inputs with arbitrary finite reference. Then the regularization converges and satisfies
--
--   $$E_C(T)=\lim_{n\to\infty}\frac{E_F(T^{\otimes n})}{n}\le E_F(T).$$
--
--   The quantity $E_C(T)$ is an upper bound on the two-way assisted private capacity and is a strong-converse bound: for every private-state generation code sequence with $m_\nu\to\infty$ and $k_\nu/m_\nu\to R>E_C(T)$, the half trace-norm error tends to one. Codes start separably, use arbitrary finite local workspace and two-way LOCC, and target private states with key dimension $2^{k_\nu}$ and equal shields.
--
--   This extends the entanglement-cost strong converse to private communication.
--
--   **Formalization Note** The state formation formula printed with a supremum is corrected to the infimum defining the named measure; see the source-correction audit.
-- source:
--   Relative Entropy Bounds on Quantum, Private and Repeater Capacities, arXiv:1604.03448v2, PDF p. 9, Theorem II.4

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P25

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Support50.P21 (eMax)

variable {I J A B C D : Type}

variable [Fintype I] [DecidableEq I] [Nonempty I]

variable [Fintype J] [DecidableEq J] [Nonempty J]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

/-- Theorem II.4, PDF p.9: regularized cost converges, is at most single-letter
formation, and is a private strong-converse bound. The printed formation sup
is corrected to inf as documented above and in MODERATION_NOTES.md. -/
theorem entanglementCost_private_strongConverse (T : Superop I J) (hT : IsChannel T) :
    Tendsto (formationQuotients T) atTop (nhds (regularizedFormationCost T)) ∧
    regularizedFormationCost T ≤ channelFormationSupremum T ∧ PrivateStrongConverseBound T (regularizedFormationCost T) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P25

end
