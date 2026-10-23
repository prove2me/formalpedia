-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_opennessLiftedSubnets
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.opennessLiftedSubnets
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:19:33.473111+00:00
-- url     : https://prove2.me/theorems/2254a5f4-af2d-48a9-8948-aa99c222b3a0
-- title:
--   Lemma 6: openness criterion using lifted subnets
-- statement:
--   Let $X$ be any topological space, $Y$ a metric space, and $\phi:X\to Y$ any map. Then $\phi$ is open if and only if every $x_0\in X$ and sequence $y_n\to\phi(x_0)$ admit a nonempty directed index set $D$, a map $n:D\to\mathbb N$ eventually exceeding every natural number, and a net $x_d\to x_0$ such that
--   $$\phi(x_d)=y_{n(d)}\quad(d\in D).$$
--
--
--   The lift uses a subnet rather than a subsequence; continuity and surjectivity are not hypotheses.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 24, Lemma 6: openness criterion using lifted subnets

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P10

noncomputable section

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology ENNReal BigOperators

universe u v w

namespace QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Dependency50.P25

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperBorel

/-- Lemma 6, PDF p.24: openness is equivalent to lifting a subnet of every
sequence converging to phi(x0), with lifts tending to x0. -/
theorem opennessLiftedSubnets {X : Type u} {Y : Type v}
    [TopologicalSpace X] [MetricSpace Y] (phi : X → Y) :
    IsOpenMap phi ↔ LiftedSubnetProperty phi := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P10

end
