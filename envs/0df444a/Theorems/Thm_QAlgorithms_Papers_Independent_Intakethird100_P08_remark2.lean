-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P08_remark2
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P08.remark2
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:25:42.720484+00:00
-- url     : https://prove2.me/theorems/cdca76c0-05e2-4b41-bc3c-102ec240c20c
-- title:
--   A Borel section continuous near identity for Lindelof quotient
-- statement:
--   Let $K,E,Q$ be topological groups in a locally split short exact sequence $1\to K\xrightarrow{i}E\xrightarrow{p}Q\to1$. Thus $i$ is a continuous closed embedding, $p$ is continuous, open and surjective, $i(K)=\ker p$, and $p$ admits a continuous section on an open neighborhood of the identity of $Q$.
--
--   Assume that $Q$ is Lindelof, meaning that every open cover has a countable subcover, and use the Borel sigma algebras. There is an everywhere-defined map $\sigma:Q\to E$ such that
--   $$
--   p\circ\sigma=\operatorname{id}_Q,\qquad \sigma\text{ is Borel measurable},\qquad \sigma|_U\text{ is continuous for some open }U\ni1.
--   $$
--   This is the countable-cover form of the global section construction.
-- source:
--   On Cohomology theory for topological groups, arXiv:1009.4519v1, PDF p. 10, Remark 2: the Lindelof section construction

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P08

namespace QAlgorithms.Papers.Independent.Intakethird100.P08

open Set MeasureTheory

open scoped BigOperators Topology CompactlySupported

section Sections

variable {K E Q : Type*} [Group K] [Group E] [Group Q]
  [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace Q]
  [IsTopologicalGroup K] [IsTopologicalGroup E] [IsTopologicalGroup Q]

/-- Remark 2, PDF p. 10: the Lindelof version of Lemma 1. The section is
Borel measurable globally, is continuous near identity, and is a right inverse;
it is not required to be a homomorphism. -/
theorem remark2 [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Q] [BorelSpace Q] [LindelofSpace Q]
    (i : K →* E) (p : E →* Q) (h : IsLocallySplitSequence i p) :
    ∃ sigma : Q → E, Measurable sigma ∧ (∀ q, p (sigma q) = q) ∧
      ∃ U : Set Q, IsOpen U ∧ 1 ∈ U ∧ ContinuousOn sigma U := by sorry

end Sections

end QAlgorithms.Papers.Independent.Intakethird100.P08
