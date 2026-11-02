-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P96_commuting_block_multiplicities
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P96.commuting_block_multiplicities
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:35:44.601541+00:00
-- url     : https://prove2.me/theorems/545e7912-0a8a-41d2-8aaa-a8f84daa54b7
-- title:
--   Commuting block algebras decompose into joint representation copies
-- statement:
--   Let $H=\mathbb C^D$, and let $A\cong\bigoplus_\mu M_{n_\mu}(\mathbb C)$ and $B\cong\bigoplus_\nu M_{m_\nu}(\mathbb C)$ be commuting complex star subalgebras of $B(H)$ with the common ambient identity. All block sizes are positive. There are nonnegative integer multiplicities $r_{\mu\nu}$ and a unitary identification
--
--   $$H\cong\bigoplus_{\mu,\nu}(\mathbb C^{n_\mu}\otimes\mathbb C^{m_\nu}\otimes\mathbb C^{r_{\mu\nu}})$$
--
--   under which every product $ab$ acts blockwise as $a_\mu\otimes b_\nu\otimes I_{r_{\mu\nu}}$. In particular,
--
--   $$\sum_{\mu,\nu}r_{\mu\nu}n_\mu m_\nu=D.$$
--
--   Blocks with zero multiplicity are absent. The multiplicities count copies in the Hilbert space representation, not repeated simple ideals of the generated algebra $AB$.
--
--   **Formalization Note** The common-identity convention is made explicit (correction C3); it is needed for the displayed dimension identity to account for all of $H$.
-- source:
--   Reversible quantum cellular automata, arXiv:quant-ph/0405174v1, PDF p. 18, Proposition 13: commuting matrix-block subalgebras and multiplicities

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P96

noncomputable section

open scoped TensorProduct Kronecker BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P96

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

/-- Proposition 13, PDF p.18: joint blocks with representation multiplicities.
Correction C3 (printed / changed / why): the printed proposition only says
"commuting subalgebras of B(H)". Here both embeddings preserve the ambient identity,
as in §IV.D. Without this condition, A = B = C E_11 in M_2 has one represented
one-dimensional joint block and an unrepresented complement, contradicting the
claimed dimension accounting. Only this common-identity condition is added;
individual joint blocks may still have multiplicity zero.
The unitary formula specifies every product, hence the generated algebra AB. -/
theorem commuting_block_multiplicities (D aCount bCount : ℕ)
    (n : Fin aCount → ℕ) (m : Fin bCount → ℕ)
    (hn : ∀ i, 0 < n i) (hm : ∀ j, 0 < m j)
    (Phi : ((i : Fin aCount) → Mat (n i)) →⋆ₐ[ℂ] Mat D)
    (Psi : ((j : Fin bCount) → Mat (m j)) →⋆ₐ[ℂ] Mat D)
    (hPhi : Function.Injective Phi) (hPsi : Function.Injective Psi)
    (hcomm : ∀ a b, Commute (Phi a) (Psi b)) :
    ∃ r : Fin aCount → Fin bCount → ℕ,
      (∑ i, ∑ j, r i j * n i * m j) = D ∧
      ∃ e : Fin D ≃ jointBlockIndex n m r,
      ∃ W : Matrix.unitaryGroup (Fin D) ℂ,
      ∀ a b, star (W : Mat D) * (Phi a * Psi b) * (W : Mat D) =
        (jointAction r a b).submatrix e e := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P96

end
