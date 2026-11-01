-- Prove2me | Theorems.Thm_WildeQIT_QErasure_tensorPower_antidegradable
-- name    : WildeQIT.QErasure.tensorPower_antidegradable
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:38:22.835895+00:00
-- url     : https://prove2.me/theorems/464887fa-6d58-4d60-8364-59a3366cf6c5
-- title:
--   Proposition 24.7.1 (proof, p. 677): $\mathcal N^{\otimes n}$ is antidegradable if $\mathcal N$ is
-- statement:
--   Let $\mathcal N_{A'\to B}$ be a quantum channel and $n\in\mathbb N$. If $\mathcal N$ is antidegradable, then so is the tensor-power channel $\mathcal N^{\otimes n}$:
--
--   $$
--   \mathcal N\ \text{antidegradable}\;\Longrightarrow\;\mathcal N^{\otimes n}\ \text{antidegradable}.
--   $$
--
--   With Exercise 13.5.6 this shows that the regularized coherent information of an antidegradable channel vanishes, hence so does its quantum capacity.
--
--   **Formalization Note** $\mathcal N^{\otimes n}$ has Kraus operators $K_{i_1}\otimes\cdots\otimes K_{i_n}$; its complementary channel is that of its own canonical isometric extension. At $n=0$ the channel is the identity on a one-dimensional system.
--
--   Differences from the source: none.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, proof of Proposition 24.7.1, p. 677

import Definitions.Def_WildeQIT_QErasure_IsAntidegradable
import Definitions.Def_WildeQIT_Degradable_tensorPower

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, proof of Proposition 24.7.1,
p. 677 ("the fact that `N^{⊗n}` is antidegradable if `N` is").
-/

namespace WildeQIT.QErasure

/-- **Proof of Proposition 24.7.1, p. 677** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8): "the fact that `N^{⊗n}` is antidegradable if `N` is". For every quantum channel
`N` and every `n`, if `N` is antidegradable (Definition 13.5.3) then so is `N^{⊗n}`.

**Formalization Note.** `N^{⊗n}` is `tensorPower N n`, on the systems `Fin n → a` and `Fin n → b`,
with Kraus operators `K_{i₁} ⊗ ⋯ ⊗ K_{iₙ}`; its complementary channel is that of its own canonical
isometric extension (environment `Fin n → N.ι`). At `n = 0` the channel is the identity on a
one-dimensional system. -/
theorem tensorPower_antidegradable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (N : QChannel a b) (hN : IsAntidegradable N) (n : ℕ) :
    IsAntidegradable (WildeQIT.Degradable.tensorPower N n) := by sorry

end WildeQIT.QErasure
