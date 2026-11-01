-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P95_four_erasure_logical_count
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P95.four_erasure_logical_count
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:49:50.037991+00:00
-- url     : https://prove2.me/theorems/61bb9a0e-8ebc-46be-a69b-cd4e246b6441
-- title:
--   Logical-generator count after four erasures
-- statement:
--   Let an $[[n,k]]$ qubit stabilizer code be represented, after removing scalar phases, by its isotropic stabilizer label subspace $S\subseteq\mathbb F_2^{2n}$, with $\dim S+k=n$. For a physical region $A$, let $\ell(A)$ be the dimension of the subspace of logical Pauli classes representable within $A$: these are centralizing Pauli labels supported in $A$, modulo stabilizer labels. If $|A^{\mathrm c}|=4$, then
--
--   $$\ell(A)\ge2k-8,$$
--
--   or equivalently $2k\le\ell(A)+8$. The independent logical classes need not commute, and this count does not identify a collection of recovered logical tensor factors. It is the general four-erasure bound, distinct from the more restrictive unpinned footnote refinement.
-- source:
--   Holographic quantum error-correcting codes: Toy models for the bulk/boundary correspondence, arXiv:1503.06237v2, PDF p. 61, Appendix E.1: logical-generator count after erasing four qubits

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P95

namespace QAlgorithms.Papers.Independent.Intakenext100.P95

open scoped Matrix ComplexConjugate

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- PDF p.61, Appendix E.1: deleting four qubits leaves at least 2k−8 independent
logical Pauli classes representable on A. S is the isotropic phase-free stabilizer
space of an [[n,k]] code; dim(S)+k=n states its dimension. The inequality avoids
natural subtraction, including codes with k<4. No identification of recovered
logical tensor factors, nor mutual commutativity of the classes, is asserted. -/
theorem four_erasure_logical_count (n k : ℕ)
    (S : Submodule (ZMod 2) (BinaryPhaseSpace n))
    (hisotropic : ∀ a ∈ S, ∀ b ∈ S, SparsePauliNoise.symplecticPairing a b = 0)
    (hdimension : Module.finrank (ZMod 2) S + k = n)
    (A : Finset (Fin n)) (herased : (Aᶜ).card = 4) :
    2 * k ≤ logicalSupportDimension S A + 8 := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P95
