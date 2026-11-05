-- Prove2me | Theorems.Thm_RepGQML_complete_reducibility
-- name    : RepGQML.complete_reducibility
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:45:04.00154+00:00
-- url     : https://prove2.me/theorems/db0b55aa-c09a-4c31-92e9-6a4cb3f72987
-- title:
--   Theorem 4 — finite dimensional unitary representations are completely reducible, with orthogonal summands
-- statement:
--   Let $G$ be a group and $R$ a unitary representation of $G$ on a finite dimensional real or complex inner product space $V$. Then $R$ is completely reducible: there are invariant subspaces $W_1,\dots,W_n$ with
--   $$
--   V=W_1\oplus\cdots\oplus W_n ,
--   $$
--   each restriction $R|_{W_j}$ being irreducible. The $W_j$ can moreover be chosen pairwise orthogonal.
--
--   This is the existence half of the block diagonalization on which Theorem 7 rests.
--
--   Differences from the source:
--   - generalization: a finite dimensional unitary representation (of a Lie group, Def 15) → a finite dimensional unitary representation of any group, over RCLike; reason: every Lie group is a group; the Lie structure plays no part; Def 6 allows real or complex V
--   - generalization: a direct sum of invariant subspaces (Def 14) → the same conclusion, and in addition the summands can be taken pairwise orthogonal; reason: the first conjunct is Theorem 4 itself; the orthogonal form is what the grouping into multiplicities uses
--   - encoding: irreducible (Def 13, read literally, also admits V = 0) → Representation.IsIrreducible, which requires a nonzero space; reason: Mathlib convention; a zero summand adds nothing, and V = 0 has the empty decomposition
-- source:
--   Ragone et al., Representation Theory for Geometric Quantum Machine Learning, arXiv:2210.07980v2, Theorem 4, p.23

import Mathlib
import Definitions.Def_RepGQML_IsUnitaryRep
import Definitions.Def_RepGQML_IsCompletelyReducible

namespace RepGQML

/-- **Theorem 4** (Ragone et al., *Representation Theory for Geometric Quantum Machine Learning*, arXiv:2210.07980v2, p.23): any finite dimensional unitary representation is completely
reducible. The summands can moreover be taken pairwise orthogonal.

**Formalization Note** `𝕜` is real or complex, as Def 6 (p.9) allows, and `G` is any group. Orthogonality
of the summands is an addition to the page's conclusion. -/
theorem complete_reducibility {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V] (ρ : Representation 𝕜 G V)
    (hρ : IsUnitaryRep ρ) :
    IsCompletelyReducible ρ ∧
      ∃ (n : ℕ) (W : Fin n → Subrepresentation ρ), IsIrreducibleSplitting ρ W ∧
        Pairwise fun i j => (W i).toSubmodule.IsOrtho (W j).toSubmodule := by sorry

end RepGQML
