-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P08_denseOpenSection
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P08.denseOpenSection
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:26:39.984122+00:00
-- url     : https://prove2.me/theorems/7d3109e2-0486-4e92-ab48-6ac3f06daba2
-- title:
--   Extension of a local section to an open dense domain
-- statement:
--   Let $K,E,Q$ be topological groups in a locally split short exact sequence $1\to K\xrightarrow{i}E\xrightarrow{p}Q\to1$. Thus $i$ is a continuous closed embedding, $p$ is continuous, open and surjective, $i(K)=\ker p$, and $p$ admits a continuous section on an open neighborhood of the identity of $Q$.
--
--   Fix an open identity neighborhood $U\subseteq Q$ and a continuous section $\sigma:U\to E$. There exist an open dense subset $V\subseteq Q$ containing $U$ and a continuous section $\tau:V\to E$ extending $\sigma$:
--   $$
--   U\subseteq V,\qquad \overline V=Q,\qquad p\circ\tau=\operatorname{id}_V,\qquad \tau|_U=\sigma.
--   $$
--   The domain may omit a closed nowhere dense subset of the quotient.
-- source:
--   On Cohomology theory for topological groups, arXiv:1009.4519v1, PDF p. 11, Section 3.4: extension to a dense open set

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P08

namespace QAlgorithms.Papers.Independent.Intakethird100.P08

open Set MeasureTheory

open scoped BigOperators Topology CompactlySupported

section Sections

variable {K E Q : Type*} [Group K] [Group E] [Group Q]
  [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace Q]
  [IsTopologicalGroup K] [IsTopologicalGroup E] [IsTopologicalGroup Q]

/-- Section 3.4, PDF p. 11: a continuous local section extends continuously to
an open dense domain, retaining its original values. No measurable gluing of
an uncountable cover of the entire quotient is asserted. -/
theorem denseOpenSection (i : K →* E) (p : E →* Q)
    (h : IsLocallySplitSequence i p) (U : Set Q) (hU : IsOpen U) (h1 : 1 ∈ U)
    (sigma : U → E) (hc : Continuous sigma) (hs : ∀ u, p (sigma u) = u.val) :
    ∃ V : Set Q, IsOpen V ∧ Dense V ∧ ∃ hUV : U ⊆ V,
      ∃ tau : V → E, Continuous tau ∧ (∀ v, p (tau v) = v.val) ∧
        ∀ u : U, tau ⟨u.val, hUV u.property⟩ = sigma u := by sorry

end Sections

end QAlgorithms.Papers.Independent.Intakethird100.P08
