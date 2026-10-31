-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P24_canonical_transform_inclusion
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P24.canonical_transform_inclusion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:55:55.188986+00:00
-- url     : https://prove2.me/theorems/1b5d5090-e452-41ca-ae72-d303dc561178
-- title:
--   Claim 1: inclusion for the canonical transforms
-- statement:
--   Let $H$ be an arbitrary complex Hilbert space and $T$ a closed densely defined normal operator on $H$. Define the source-constructed operators
--
--   $$
--   A=(I+T^*T)^{-1},\qquad B=TA.
--   $$
--
--   Then
--
--   $$
--   AT\subseteq B.
--   $$
--
--   Operator inclusion means inclusion of domains and agreement of the actions on the smaller domain. Products have their maximal natural composition domains. This is the claim concerning these particular transforms inside the proof of the decomposition theorem.
--
--   **Source correction.** As in the decomposition theorem, closedness is added to the printed definition of normality because the preceding construction and proof use it.
-- source:
--   Decomposition of Normal Operators and Its Application to Spectral Theorem, arXiv:2006.04644v2, PDF p. 2, Section 2, Claim 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P24

noncomputable section

attribute [local instance] Classical.propDecidable

open Set MeasureTheory

open scoped Topology

open QAlgorithms.Papers.Independent.Claimed50.P05

namespace QAlgorithms.Papers.Independent.Intakenext100.P24

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Section 2, Claim 1, PDF p.2: AT is contained in B for the constructed
A = (I + T*T)^(-1), B = TA, not arbitrary bounded witnesses.
Source correction requiring independent moderation:
Printed: normality in Definition 2.1 omits closedness.
Changed: require closed densely defined normal T via accepted Normal.
Why: the preceding construction invokes Theorem 2.2 and uses closedness;
identity on c00 in l2 invalidates the literal unclosed reading. -/
theorem canonical_transform_inclusion (T : Relation H) (hT : Normal (k := ℂ) T) :
    mul (transformT (k := ℂ) T) T ⊆ transformS (k := ℂ) T := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P24

end
