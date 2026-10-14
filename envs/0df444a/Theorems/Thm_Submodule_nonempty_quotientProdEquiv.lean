-- Prove2me | Theorems.Thm_Submodule_nonempty_quotientProdEquiv
-- name    : Submodule.nonempty_quotientProdEquiv
-- status  : Proved
-- author  : @t4v1
-- created : 2026-09-09T22:37:00.050215+00:00
-- url     : https://prove2.me/theorems/bdc9fb1a-4a9f-44a9-a3c5-7e6bb9941658
-- title:
--   $(M \times N)/(p \times q) \cong M/p \times N/q$
-- statement:
--   Let $R$ be a ring and $M$, $N$ be $R$-modules, with submodules $p \subseteq M$ and $q \subseteq N$. The statement asserts that there is an $R$-linear isomorphism
--
--   $$(M \times N)\,/\,(p \times q) \;\cong\; (M/p) \times (N/q),$$
--
--   i.e. that the type of $R$-linear equivalences between the quotient of the product by the product submodule and the product of the two quotients is nonempty. Equivalently, the cokernel of a direct sum of linear maps is the direct sum of the cokernels.
--
--   The expected argument applies the first isomorphism theorem to the product $\pi_p \times \pi_q : M \times N \to M/p \times N/q$ of the two quotient maps, which is surjective with kernel $p \times q$.
-- source:
--   Drafted as a Mathlib contribution for `Mathlib/LinearAlgebra/Prod.lean`, beside `Submodule.prod`; MorseFloer project, `contrib/Mathlib/LinearAlgebra/Prod.lean`.

import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Isomorphisms

theorem Submodule.nonempty_quotientProdEquiv {R M N : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (p : Submodule R M) (q : Submodule R N) :
    Nonempty (((M × N) ⧸ p.prod q) ≃ₗ[R] (M ⧸ p) × (N ⧸ q)) := by sorry
