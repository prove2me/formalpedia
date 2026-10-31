-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P14_dimension_shifting_identity
-- name    : QAlgorithms.Papers.Independent.Intake100.P14.dimension_shifting_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:19:03.334843+00:00
-- url     : https://prove2.me/theorems/ef98be10-6149-46a8-b18c-63b5fa72c339
-- title:
--   Explicit dimension-shifting identity
-- statement:
--   Let $G$ be a Hausdorff locally compact second countable group, let $A$ be a Polish Abelian topological group with a jointly continuous action $T$ by automorphisms, and let $p\ge1$. Cochains are Borel maps on $G^p$, cocycle and coboundary equations hold Haar almost everywhere, and $d$ is the unnormalized inhomogeneous bar differential. In degree zero, $C^0=A$ and $B^0=0$. For a Borel $p$-cocycle $\psi$, define $Q\psi$ by the signed last-coordinate formula
--
--   $$Q\psi(g_1,\ldots,g_{p-1})(h)=(-1)^p\psi(g_1,\ldots,g_{p-1},(g_1\cdots g_{p-1})^{-1}h).$$
--
--   On functions $G\to A$ use $(R(g)f)(h)=T(g)f(g^{-1}h)$. Then, for almost every $g\in G^p$ and almost every $h\in G$,
--
--   $$d(Q\psi)(g)(h)=\psi(g).$$
--
--   Thus its coboundary is the constant-valued image of $\psi$. This is the explicit cochain identity underlying dimension shifting.
-- source:
--   Continuity properties of measurable group cohomology, arXiv:1004.4937v4, PDF p. 14, Unnumbered §3.1: explicit dimension-shifting identity

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

/-- Section 3.1, PDF p.14: the explicit dimension-shifting identity in every positive
degree, including degree one; no degree-one shifted-group isomorphism is asserted. -/
theorem dimension_shifting_identity (p : ℕ) (f : GroupPower G (p + 1) → A)
    (hf : IsCocycle mu T.act (p + 1) f) :
    ∀ᵐ g ∂powerMeasure mu (p + 1), ∀ᵐ h ∂mu,
      barDifferential (coinducedAction T.act) p (dimensionShiftQ p f) g h = f g := by sorry

end LocallyCompact

end QAlgorithms.Papers.Independent.Intake100.P14

end
