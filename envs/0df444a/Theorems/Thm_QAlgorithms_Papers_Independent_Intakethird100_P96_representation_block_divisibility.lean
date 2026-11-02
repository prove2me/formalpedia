-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P96_representation_block_divisibility
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P96.representation_block_divisibility
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:34:09.313285+00:00
-- url     : https://prove2.me/theorems/7d4aed29-6e2a-4e86-985c-3290514ed050
-- title:
--   Unital matrix representations have divisible block sizes
-- statement:
--   Let $d\ge1$ and let $n_\mu\ge1$ be positive integers indexed by a finite set. If $\Phi:M_d(\mathbb C)\to\bigoplus_\mu M_{n_\mu}(\mathbb C)$ is a complex-linear star homomorphism preserving the identity, then
--
--   $$d\mid n_\mu\qquad\text{for every }\mu.$$
--
--   The target index set may be empty, in which case the conclusion is vacuous. Unitality is essential to the representation dimension constraint.
-- source:
--   Reversible quantum cellular automata, arXiv:quant-ph/0405174v1, PDF p. 18, Proposition 12: divisibility of dimensions of matrix representations

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P96

noncomputable section

open scoped TensorProduct Kronecker BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P96

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

/-- Proposition 12, PDF p.18: unital representation block sizes are divisible by `d`. -/
theorem representation_block_divisibility (d : ℕ) (hd : 0 < d)
    (count : ℕ) (n : Fin count → ℕ) (hn : ∀ i, 0 < n i)
    (Phi : Mat d →⋆ₐ[ℂ] ((i : Fin count) → Mat (n i))) :
    ∀ i, d ∣ n i := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P96

end
