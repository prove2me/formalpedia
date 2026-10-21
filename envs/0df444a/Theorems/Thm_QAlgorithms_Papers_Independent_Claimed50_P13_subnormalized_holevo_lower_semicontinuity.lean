-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P13_subnormalized_holevo_lower_semicontinuity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P13.subnormalized_holevo_lower_semicontinuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:40:51.968082+00:00
-- url     : https://prove2.me/theorems/f38df6fe-6028-4794-8468-2dcb0d39062c
-- title:
--   Section 6 unnumbered extension: lower semicontinuity on subnormalized ensembles
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, channels are complex-linear completely positive trace-preserving maps on the full trace class, and all logarithms are natural. Let $\mathfrak T_1(H)=\{A\ge0:A\text{ is trace class},\operatorname{Tr}A\le1\}$, with trace norm. For a Borel probability law $\mu$ on this space, put $\overline A=\int A\,d\mu$ and $\chi(\mu)=\int D(A\Vert\overline A)\,d\mu$, where relative entropy includes the correction $\operatorname{Tr}(B-A)$. Then
--
--   $$\mu\longmapsto\chi(\mu)\quad\text{is lower semicontinuous in the weak probability topology}.$$
--
--   This extends the ensemble semicontinuity framework to trace-decreasing outputs.
-- source:
--   On the entanglement-assisted classical capacity of infinite-dimensional quantum channels, arXiv:1210.6926v2, PDF p. 20, Section 6 unnumbered extension: lower semicontinuity on subnormalized ensembles

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

namespace QAlgorithms.Papers.Independent.Claimed50.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section 6 extension, PDF pp.20--21: weak laws on the trace-norm T_1(H).
No finiteness hypothesis is imposed. -/
theorem subnormalized_holevo_lower_semicontinuity {I : Type} [Countable I] [Nonempty I] :
    LowerSemicontinuous (subnormalizedHolevo (I := I)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P13

end
