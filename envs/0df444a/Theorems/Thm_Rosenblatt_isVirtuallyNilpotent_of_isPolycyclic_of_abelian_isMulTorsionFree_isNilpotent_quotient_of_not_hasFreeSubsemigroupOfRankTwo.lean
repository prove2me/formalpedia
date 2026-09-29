-- Prove2me | Theorems.Thm_Rosenblatt_isVirtuallyNilpotent_of_isPolycyclic_of_abelian_isMulTorsionFree_isNilpotent_quotient_of_not_hasFreeSubsemigroupOfRankTwo
-- name    : Rosenblatt.isVirtuallyNilpotent_of_isPolycyclic_of_abelian_isMulTorsionFree_isNilpotent_quotient_of_not_hasFreeSubsemigroupOfRankTwo
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-21T15:15:06.513465+00:00
-- url     : https://prove2.me/theorems/4ccbb3a2-bbc0-40f3-a2d7-c0ed5c73b166
-- title:
--   Theorem 4.12, core step: a polycyclic extension of a free abelian group by a nilpotent group, with no free subsemigroup of rank two, is almost nilpotent
-- statement:
--   Let $\Gamma$ be a polycyclic group with **no free subsemigroup of rank two**, and let
--   $A \trianglelefteq \Gamma$ be a normal subgroup which is abelian and torsion-free and for which
--   the quotient $\Gamma/A$ is nilpotent. Then $\Gamma$ is almost nilpotent.
--
--   *The conclusion* is Mathlib's `Group.IsVirtuallyNilpotent`: there is a nilpotent subgroup of
--   $\Gamma$ of finite index. That subgroup is **not** required to be normal, and "finite index"
--   means the set of left cosets is finite.
--
--   *The hypothesis on $A$* is four conditions: normality in $\Gamma$ (without which the quotient
--   would not be a group), commutativity of $A$, torsion-freeness of $A$, and nilpotency of
--   $\Gamma/A$. Two points on how the last two read.
--
--   Torsion-freeness is Mathlib's `IsMulTorsionFree`, which is literally the statement that for
--   every $n \neq 0$ the map $x \mapsto x^n$ is *injective* on $A$ — not, literally, that no
--   nontrivial element has finite order. The two agree here, but only because $A$ is assumed
--   abelian: in an abelian group $x^n = y^n$ gives $(xy^{-1})^n = 1$, so power-injectivity and the
--   absence of nontrivial elements of finite order are the same condition. In a general group they
--   are not, and the injective form is the stronger-looking one.
--
--   Nilpotency is Mathlib's `Group.IsNilpotent`, the ascending upper central series of $\Gamma/A$
--   reaching the whole group in finitely many steps.
--
--   *How this relates to Rosenblatt's own phrasing.* He reduces Theorem 4.12 to an exact sequence
--   $e \to \mathbb{Z}^k \to \Gamma \to N \to e$ with $N$ nilpotent, and then works with the canonical
--   basis of $\mathbb{Z}^k$. A finitely generated torsion-free abelian group is free abelian of
--   finite rank, and $A$ is finitely generated here because $\Gamma$ is polycyclic, so the hypothesis
--   above is that exact situation — stated through the three intrinsic conditions on $A$ rather than
--   through a choice of isomorphism to $\mathbb{Z}^k$, so that no basis is baked into the statement.
--
--   *What is not assumed.* $A$ is nowhere required to be nontrivial, proper, or of finite index, and
--   it does not appear in the conclusion. The degenerate instances are genuine and harmless: $A =
--   \{1\}$ makes the package say "$\Gamma$ nilpotent implies $\Gamma$ almost nilpotent", and $A =
--   \Gamma$ makes the quotient hypothesis empty. The hypotheses are jointly satisfiable — the trivial
--   group meets all of them — so the implication is not vacuous.
-- source:
--   Rosenblatt, J. M., Invariant measures and growth conditions, Transactions of the American Mathematical Society 193 (1974) 33–53, https://doi.org/10.1090/S0002-9947-1974-0342955-9, Theorem 4.12, pp. 48-49, the case the proof reduces to

import Definitions.Def_Chou_Growth
import Definitions.Def_MilnorWolf_Growth
import Mathlib

namespace Rosenblatt

theorem isVirtuallyNilpotent_of_isPolycyclic_of_abelian_isMulTorsionFree_isNilpotent_quotient_of_not_hasFreeSubsemigroupOfRankTwo
    {G : Type*} [Group G] (hpoly : MilnorWolf.IsPolycyclic G)
    (hfree : ¬ Chou.HasFreeSubsemigroupOfRankTwo G)
    (A : Subgroup G) [A.Normal] (hab : ∀ x y : A, x * y = y * x)
    (htf : IsMulTorsionFree A) (hnil : Group.IsNilpotent (G ⧸ A)) :
    Group.IsVirtuallyNilpotent G := by
  sorry

end Rosenblatt
