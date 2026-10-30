-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P09_abelianDelooping_reduction
-- name    : QAlgorithms.Papers.Independent.Bridge50.P09.abelianDelooping_reduction
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T12:20:19.826029+00:00
-- url     : https://prove2.me/theorems/0774629d-811d-402a-bd53-0e4e8b87a80f
-- title:
--   The reduction of the delooping of an abelian Lie group
-- statement:
--   Let $A$ be an abelian finite-dimensional real Lie group. The crossed module defining $BA$ has trivial structure group and action $\alpha(1,a)=a$. With ordinary subgroup generation, its reduction satisfies
--   $$[1,A]=\{1\},\qquad (BA)_{\mathrm{red}}=A/[1,A]\cong A.$$
--   The isomorphism is the canonical one taking the quotient class of $a$ to $a$. The statement includes the trivial group $A$ and identifies the value group for abelian reduced surface holonomy.
-- source:
--   Connections on non-abelian Gerbes and their Holonomy, arXiv:0808.1923v3, PDF p. 50, Example 5.2.3(a): reduction of BA

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P09

namespace QAlgorithms.Papers.Independent.Bridge50.P09

open scoped Manifold ContDiff

/-- Example 5.2.3(a), PDF p. 50. For an abelian Lie group `A`, the
reduction of `BA` has trivial generating subgroup and is canonically `A`.
The displayed isomorphism sends every quotient class `[a]` to `a`. -/
theorem abelianDelooping_reduction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : Type*) [CommGroup A] [TopologicalSpace A]
    [T2Space A] [SecondCountableTopology A] [ChartedSpace E A]
    [IsManifold (𝓘(ℝ, E)) ∞ A] [LieGroup (𝓘(ℝ, E)) ∞ A] :
    actionCommutatorSubgroup (trivialAction (A := A)) = ⊥ ∧
      ∃ e : (A ⧸ actionCommutatorSubgroup (trivialAction (A := A))) ≃* A,
        ∀ a : A, e (QuotientGroup.mk a) = a := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P09
