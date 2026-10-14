-- Prove2me | Theorems.Thm_Submodule_nonempty_prodEquiv
-- name    : Submodule.nonempty_prodEquiv
-- status  : Proved
-- author  : @t4v1
-- created : 2026-09-09T22:36:59.008541+00:00
-- url     : https://prove2.me/theorems/780aff9f-d111-4520-9538-6b2a74e65743
-- title:
--   The product submodule $p \times q$ is linearly isomorphic to the product module $p \times q$
-- statement:
--   Let $R$ be a ring and $M$, $N$ be $R$-modules, with submodules $p \subseteq M$ and $q \subseteq N$. Mathlib's `Submodule.prod` forms the submodule $p \times q \subseteq M \times N$, whose underlying type is a module in its own right. The statement asserts that there is an $R$-linear isomorphism
--
--   $$p \times q \;\cong\; p \times q$$
--
--   between that submodule and the product module of $p$ and $q$, i.e. that the type of $R$-linear equivalences between them is nonempty.
--
--   The expected witness sends $((m,n), h)$, where $h$ certifies $m \in p$ and $n \in q$, to the pair $((m, h_1), (n, h_2))$; every axiom of a linear equivalence holds definitionally for this map.
-- source:
--   Drafted as a Mathlib contribution for `Mathlib/LinearAlgebra/Prod.lean`, beside `Submodule.prod`; MorseFloer project, `contrib/Mathlib/LinearAlgebra/Prod.lean`.

import Mathlib.LinearAlgebra.Prod

theorem Submodule.nonempty_prodEquiv {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (p : Submodule R M) (q : Submodule R N) :
    Nonempty (p.prod q ≃ₗ[R] p × q) := by sorry
