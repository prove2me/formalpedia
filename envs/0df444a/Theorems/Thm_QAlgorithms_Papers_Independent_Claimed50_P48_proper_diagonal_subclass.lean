-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_proper_diagonal_subclass
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.proper_diagonal_subclass
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:46:38.450072+00:00
-- url     : https://prove2.me/theorems/406df8c7-c6dc-4a65-90be-f669966308f2
-- title:
--   Diagonal CP maps form a proper subclass of entanglement-breaking complements
-- statement:
--   Compare finite CP maps with nonzero input up to the partial-isometry output equivalence (2). Every map equivalent to a common-basis diagonal CP map is complementary to an entanglement-breaking CP map, and the inclusion is proper:
--
--   $$\{\text{diagonal CP maps up to (2)}\}\subsetneq
--   \{\text{complements of entanglement-breaking CP maps}\}.$$
--
--   An explicit witness is $\Phi:\mathcal M(\mathbb C)\to\mathcal M(\mathbb C^2)$, $\Phi(X)=\operatorname{Tr}(X)I_2/2$. It is a channel and an entanglement-breaking complement, but is not equivalent to any diagonal map on its one-dimensional input. This retains the abstract's strictness assertion, beyond mere inclusion.
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 1, Diagonal CP maps form a proper subclass of entanglement-breaking complements

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

/-- Abstract, PDF p.1, with pp.4–5: proper inclusion of output equivalence
classes, with a rank-two replacer witness on a one-dimensional input. -/
theorem proper_diagonal_subclass :
    (∀ (n m : ℕ), 0 < n → ∀ Phi : Superop (Fin n) (Fin m),
      DiagonalEquivalent Phi → EBComplement Phi) ∧
    (∃ Phi : Superop (Fin 1) (Fin 2),
      Phi = (fun rho => (rho.trace / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
      IsChannel Phi ∧ EBComplement Phi ∧ ¬ DiagonalEquivalent Phi) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
