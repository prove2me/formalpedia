-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P14_discrete_coefficient_union
-- name    : QAlgorithms.Papers.Independent.Intake100.P14.discrete_coefficient_union
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:14:25.163857+00:00
-- url     : https://prove2.me/theorems/6ae77bf9-09ea-4de9-9230-513c3f6aabc9
-- title:
--   Theorem C: continuity for increasing discrete coefficient unions
-- statement:
--   Let $G$ be a Hausdorff locally compact second countable group, let $A$ be a Polish Abelian topological group with a jointly continuous action $T$ by automorphisms, and let $p\ge0$. Cochains are Borel maps on $G^p$, cocycle and coboundary equations hold Haar almost everywhere, and $d$ is the unnormalized inhomogeneous bar differential. In degree zero, $C^0=A$ and $B^0=0$. Suppose $G$ is compact, $A$ is discrete, and $A_0\subseteq A_1\subseteq\cdots$ is a sequence of $G$-invariant subgroups with union $A$. Then inclusions induce an isomorphism
--
--   $$\varinjlim_m H^p_{\mathrm m}(G,A_m)\longrightarrow H^p_{\mathrm m}(G,A).$$
--
--   Equivalently, each class has a representative taking values in some $A_m$, and if an $A_m$-valued cocycle becomes a coboundary in $A$, it has a primitive in some $A_k$ with $k\ge m$. The latter condition in degree zero means equality to zero.
--
--   The two assertions express both directions of continuity under coefficient unions.
-- source:
--   Continuity properties of measurable group cohomology, arXiv:1004.4937v4, PDF p. 9, Theorem C: increasing discrete coefficient unions

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P14

noncomputable section

open MeasureTheory Filter Set

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P14

universe u v w

section LocallyCompact

variable {G : Type u} [Group G] [TopologicalSpace G]
    [hTG : IsTopologicalGroup G] [hT2 : T2Space G]
    [hLC : LocallyCompactSpace G] [hSC : SecondCountableTopology G]
    [MeasurableSpace G] [hBG : BorelSpace G]
    {A : Type v} [AddCommGroup A] [MetricSpace A] [hTA : IsTopologicalAddGroup A]
    [hPA : PolishSpace A] [MeasurableSpace A] [hBA : BorelSpace A]
    (mu : Measure G) [hHaar : mu.IsHaarMeasure] (T : ModuleAction G A)

include hTG hT2 hLC hSC hBG hTA hPA hBA hHaar

/-- Theorem C, PDF p.9, proof pp.21--22: finite-stage representatives and eventual
finite-stage primitives express surjectivity and injectivity of the direct-limit comparison.
In degree zero the boundary predicates mean equality to zero. -/
theorem discrete_coefficient_union [CompactSpace G] [DiscreteTopology A]
    (S : ℕ → AddSubgroup A) (hmono : Monotone S)
    (hunion : ∀ a : A, ∃ m : ℕ, a ∈ S m)
    (hstable : ∀ m g a, a ∈ S m → T.act g a ∈ S m) (p : ℕ) :
    (∀ f : GroupPower G p → A, IsCocycle mu T.act p f →
      ∃ m : ℕ, ∃ sigma : GroupPower G p → A, IsCocycle mu T.act p sigma ∧
        (∀ g, sigma g ∈ S m) ∧ SameClass mu T.act p f sigma) ∧
    (∀ m : ℕ, ∀ f : GroupPower G p → A, IsCocycle mu T.act p f →
      (∀ g, f g ∈ S m) → IsMeasurableBoundary mu T.act p f →
      ∃ k : ℕ, m ≤ k ∧ IsBoundaryIn mu T.act (S k) p f) := by sorry

end LocallyCompact

end QAlgorithms.Papers.Independent.Intake100.P14

end
