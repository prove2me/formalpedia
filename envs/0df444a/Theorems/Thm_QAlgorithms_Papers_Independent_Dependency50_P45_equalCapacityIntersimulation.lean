-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P45_equalCapacityIntersimulation
-- name    : QAlgorithms.Papers.Independent.Dependency50.P45.equalCapacityIntersimulation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:10:27.504978+00:00
-- url     : https://prove2.me/theorems/530dd08a-58f1-41af-80dc-3ca552a62d17
-- title:
--   Corollary 1: equal-capacity classical channel intersimulation
-- statement:
--   Let $N:X\to Y$ and $M:U\to V$ be finite-alphabet discrete memoryless channels with nonempty alphabets and equal Shannon capacity in bits. With unlimited independent shared fair randomness, each channel can simulate the other. In each direction there are deterministic channel-use budgets $m_n$ and protocols using only $m_n$ copies of the simulating channel, with stochastic kernels $S_n$, such that
--
--   $$\frac{m_n}{n}\longrightarrow1,\qquad \max_{u\in U^n}\frac12\sum_{v\in V^n}|S_n(v\mid u)-M^{\otimes n}(v\mid u)|\longrightarrow0.$$
--
--   The corresponding reversed statement also holds. Shared randomness precedes the input; Bob decodes using only the shared tape and the channel outputs. This asserts achievable unit asymptotic efficiency, including equal zero capacities, and does not assert that the optimal simulation rate is exactly one.
-- source:
--   Entanglement-assisted capacity of a quantum channel and the reverse Shannon theorem, arXiv:quant-ph/0106052v2, PDF p. 39, Corollary 1: equal-capacity classical channel intersimulation

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45

noncomputable section

open scoped ComplexConjugate Matrix

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P76 (dampingChannel)

/-- PDF p.39, Corollary 1: equal Shannon capacities give both directions of unit
asymptotic efficiency with fixed channel-use budgets and uniformly vanishing error. -/
theorem equalCapacityIntersimulation {X Y U V : Type*}
    [Fintype X] [Fintype Y] [Fintype U] [Fintype V]
    [Nonempty X] [Nonempty Y] [Nonempty U] [Nonempty V]
    (N : DMC X Y) (M : DMC U V) (hequal : shannonCapacity N = shannonCapacity M) :
    UnitSimulation N M ∧ UnitSimulation M N := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P45

end
