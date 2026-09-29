-- Prove2me | Theorems.Thm_PassivityUn_symm_antisymm_dim
-- name    : PassivityUn.symm_antisymm_dim
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-23T21:16:31.168977+00:00
-- url     : https://prove2.me/theorems/6d5b30ab-7da5-40e2-8687-ba13972ba72e
-- title:
--   $\tfrac{n(n+1)}{2} + \tfrac{n(n-1)}{2} = n^2$
-- statement:
--   For every natural number $n$,
--
--   $$
--   \frac{n(n+1)}{2} + \frac{n(n-1)}{2} = n^2 .
--   $$
--
--   The two summands are the dimensions of the spaces of symmetric and of antisymmetric real $n\times n$ matrices, so this is the arithmetic that turns the block description of the admissible class into the count $n^2$.
--
--   **Formalization Note** The identity is stated in $\mathbb{N}$ with floor division and truncated subtraction; both are exact here, since $n(n\pm1)$ is always even and $n\cdot(n-1) = 0$ at $n = 0$.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §6, Theorem 6.1: https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", Corrected Theorem 6.1(b) (dimension count): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib

namespace PassivityUn
theorem symm_antisymm_dim (n : ℕ) :
    n * (n + 1) / 2 + n * (n - 1) / 2 = n ^ 2 := by sorry
end PassivityUn
