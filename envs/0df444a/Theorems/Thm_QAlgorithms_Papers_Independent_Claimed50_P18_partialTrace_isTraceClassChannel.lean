-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_partialTrace_isTraceClassChannel
-- name    : QAlgorithms.Papers.Independent.Claimed50.P18.partialTrace_isTraceClassChannel
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-02T20:16:13.917292+00:00
-- url     : https://prove2.me/theorems/a03df428-93f2-400a-abd0-7d0e9d9998d8
-- title:
--   Partial traces are quantum channels on trace class
-- statement:
--   Let $\mathcal H_I,\mathcal H_J$ be separable complex Hilbert spaces with countable orthonormal bases indexed by $I$ and $J$. Both partial traces
--
--   $$
--   \operatorname{Tr}_J:\mathfrak T(\mathcal H_I\otimes\mathcal H_J)	o\mathfrak T(\mathcal H_I),\qquad \operatorname{Tr}_I:\mathfrak T(\mathcal H_I\otimes\mathcal H_J)	o\mathfrak T(\mathcal H_J)
--   $$
--
--   are quantum channels: they map trace-class operators to trace-class operators, are complex-linear on trace class, and are completely positive and trace preserving, i.e. for every finite ancilla $\mathbb C^n$ the amplification $\operatorname{Tr}_J\otimes\mathrm{id}_n$ (resp. $\operatorname{Tr}_I\otimes\mathrm{id}_n$) maps density operators to density operators. In the source the channels $\operatorname{Tr}_B$ and $\operatorname{Tr}_A$ on $\mathfrak T(\mathcal H_{AB})$ are the two channels whose coherent informations appear in (3) and (4).
--
--   **Formalization Note** The channel predicate is the frozen `IsTraceClassChannel` of Dependency50.P33 (trace-class preservation, additivity and $\mathbb C$-homogeneity on trace class, and `IsDensity` of `tensorApply` on every state of $(\cdot)	imes\mathrm{Fin}\,n$). The partial traces are the coefficientwise series `traceSecond` $(\operatorname{Tr}_J X)_{ii'}=\sum_{j}X_{(i,j),(i',j)}$ and `traceFirst` $(\operatorname{Tr}_I X)_{jj'}=\sum_{i}X_{(i,j),(i,j')}$ of Frontier18.P01.
-- source:
--   Kuznetsova, Quantum conditional entropy for infinite-dimensional systems, arXiv:1004.4519v2, PDF p. 2, §1, identities (3)-(4) (the channels Tr_B and Tr_A); Holevo, Quantum Systems, Channels, Information (2nd ed.), Section 6.4, partial trace as a channel

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P18

noncomputable section

open Filter

open scoped ENNReal BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01

open QAlgorithms.Papers.Independent.Frontier18.P08 (operatorTrace)

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P18

theorem partialTrace_isTraceClassChannel {I J : Type} [Countable I] [Countable J] :
    IsTraceClassChannel (@traceSecond I J) ∧ IsTraceClassChannel (@traceFirst I J) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P18

end
