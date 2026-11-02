-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P59_torsor_cylinder_pullback
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P59.torsor_cylinder_pullback
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:26:15.035114+00:00
-- url     : https://prove2.me/theorems/f03cb5e5-277e-408c-9216-d16eb77a55f2
-- title:
--   Right principal bundles over a paracompact cylinder are pulled back
-- statement:
--   Let $G$ be a compactly generated topological group and $T$ a compactly generated paracompact space. All principal bundles below are locally trivial right $G$-bundles in compactly generated spaces. For every such bundle $P\to[0,1]\times T$, there are a right principal $G$-bundle $Q\to T$ and a $G$-equivariant homeomorphism over $[0,1]\times T$:
--
--   $$
--   P\cong\operatorname{pr}_T^*Q.
--   $$
--
--   The bundle $Q$ need not be trivial. This identifies cylinder families with pullbacks from the parameter space, without requiring connectedness or discreteness of $G$.
--
--   **Formalization Note** Products, subspaces, and the pullback carry compactly generated topologies. The isomorphism preserves the projection and the right action. The Milnor classifying space mentioned in the source is used in the proof and is not additional input to the statement.
-- source:
--   Mapping stacks of topological stacks, arXiv:0809.2373v2, PDF p. 12, Lemma 7.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P59

namespace QAlgorithms.Papers.Independent.Intakethird100.P59

universe u v

/-- Lemma 7.1, PDF p.12. Every right G-torsor over the cylinder on a
paracompact CGTop space is isomorphic over the cylinder to a pulled-back torsor.
The homeomorphism preserves both the base projection and the right action.
The Milnor space mentioned in the source is a proof tool, not input data. -/
theorem torsor_cylinder_pullback
    (G T E : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactlyGeneratedSpace G] [TopologicalSpace T] [CompactlyGeneratedSpace T]
    [ParacompactSpace T] [TopologicalSpace E] [CompactlyGeneratedSpace E]
    (p : C(E, (Set.Icc (0 : ℝ) 1) × T)) (a : RightAction G E)
    (hp : IsRightPrincipal p a) :
    ∃ (Q : Type u) (tQ : TopologicalSpace Q),
      letI := tQ
      ∃ (_ : CompactlyGeneratedSpace Q) (q : C(Q, T)) (b : RightAction G Q),
        IsRightPrincipal q b ∧
        ∃ h : E ≃ₜ CylinderPullback q,
          (∀ e, (h e).1.1 = p e) ∧
          (∀ e g, (h (a.act e g)).1.2 = b.act (h e).1.2 g) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P59
