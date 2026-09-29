-- Prove2me | Theorems.Thm_Rosenblatt_isVirtuallyNilpotent_or_hasFreeSubsemigroupOfRankTwo_of_isPolycyclic
-- name    : Rosenblatt.isVirtuallyNilpotent_or_hasFreeSubsemigroupOfRankTwo_of_isPolycyclic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-21T14:39:14.948097+00:00
-- url     : https://prove2.me/theorems/e0be8055-c3c0-4a33-ae4d-89858e5cbf70
-- title:
--   Theorem 4.12: a polycyclic group is almost nilpotent or contains a free subsemigroup of rank two
-- statement:
--   Let $\Gamma$ be a polycyclic group. Then $\Gamma$ is almost nilpotent **or** $\Gamma$
--   contains a free subsemigroup of rank two.
--
--   *The hypothesis.* Polycyclic is taken in the published sense of Wolf's Proposition 4.1 (1):
--   subgroups $\Gamma = A_0 \supseteq A_1 \supseteq \cdots \supseteq A_t = \{1\}$ with each $A_{i+1}$
--   normal in $A_i$ and each $A_i/A_{i+1}$ cyclic. Normality is relative to the preceding term only,
--   so the series is subnormal; "cyclic" includes the trivial and the finite cyclic groups; and the
--   chain need not descend strictly. Nothing else is assumed of $\Gamma$ — in particular finite
--   generation is not assumed separately, being a consequence of the hypothesis.
--
--   *The conclusion* is a disjunction of the following two statements.
--
--   "Almost nilpotent" is Mathlib's `Group.IsVirtuallyNilpotent`: there exists a nilpotent subgroup
--   of $\Gamma$ of finite index. The subgroup is **not** required to be normal, and "finite index"
--   means the coset space is finite. Taking $\Gamma$ itself shows a nilpotent group is almost
--   nilpotent, and taking any finite group shows a finite group is.
--
--   "Contains a free subsemigroup of rank two" is: there exist $a, b \in \Gamma$ such that distinct
--   **positive** words in two letters take distinct values when the letters are read as $a$ and $b$,
--   multiplied left to right, the empty word sent to $1$. No letter stands for an inverse and no
--   cancellation occurs, so this asserts a free sub*semigroup* and not a free subgroup of rank two;
--   it does force $a \neq b$, both of infinite order, and $\Gamma$ infinite.
--
--   *What is and is not asserted.* The disjunction is **inclusive**: the statement asserts that at
--   least one alternative holds, and says nothing about whether both can hold, which one holds, or
--   how to tell. Rosenblatt's own Theorem 4.12 adds "but not both". That exclusivity is a separate
--   assertion and is deliberately not made here: ruling out a free subsemigroup in an almost
--   nilpotent group needs the polynomial-growth half of Wolf's Theorem 3.2, which is not yet
--   available in the library, whereas the inclusive disjunction is exactly what Chou's argument on
--   p. 401 consumes. The statement is a one-directional implication, not an equivalence; the
--   converse is not asserted.
-- source:
--   Rosenblatt, J. M., Invariant measures and growth conditions, Transactions of the American Mathematical Society 193 (1974) 33–53, https://doi.org/10.1090/S0002-9947-1974-0342955-9, Theorem 4.12, p. 45

import Definitions.Def_Chou_Growth
import Definitions.Def_MilnorWolf_Growth
import Mathlib

namespace Rosenblatt

theorem isVirtuallyNilpotent_or_hasFreeSubsemigroupOfRankTwo_of_isPolycyclic {G : Type*}
    [Group G] (h : MilnorWolf.IsPolycyclic G) :
    Group.IsVirtuallyNilpotent G ∨ Chou.HasFreeSubsemigroupOfRankTwo G := by
  sorry

end Rosenblatt
