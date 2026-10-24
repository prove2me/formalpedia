-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_unruh_capacity_shape
-- name    : QAlgorithms.Papers.Independent.Support50.P01.unruh_capacity_shape
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:14:16.098715+00:00
-- url     : https://prove2.me/theorems/1a323990-45d3-4ed9-98d2-9cc5449b8463
-- title:
--   §III.B, Fig.1: positivity, monotonicity, convexity and endpoints
-- statement:
--   For $0<z<1$, let $\mathcal N_z$ be the full Unruh channel of Eqs.(11),(12), with receiver $\bigoplus_{k\ge0}\mathbb C^{k+2}$, genuine environment $\bigoplus_{k\ge0}\mathbb C^{k+1}$, and the common flagged dilation of the $1\to k+1$ cloning sectors with weights $p_k(z)=(1-z)^3z^k(k+1)(k+2)/2$. Use the entire countable sums, bit entropies, and unrestricted entangled density inputs for every positive block length. Write $Q(z)$ for the regularized optimized coherent information of this channel. On $0<z<1$,
--   $$
--   Q(z)>0,\qquad Q\text{ is nonincreasing and convex},\qquad
--   \lim_{z\downarrow0}Q(z)=1,\quad\lim_{z\uparrow1}Q(z)=0.
--   $$
--   These are one-sided limits. No value of a channel at $z=1$ or numerical curvature constant is asserted.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 8, §III.B, Fig.1: positivity, monotonicity, convexity and endpoints

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P01

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable dilationPower maximumCoherentInformation)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation quantumCapacity)

open QAlgorithms.Papers.Independent.Information100.P08 (maximallyMixed)

open QAlgorithms.Papers.Independent.Dependency50.P41 (EntanglementBreaking)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {a b e c : ℕ}

/-- PDF pp.7–8, Fig.1: positivity, monotonicity, convexity and one-sided endpoints.
There is no z=1 channel and no substitution into a divergent entropy sum. -/
theorem unruh_capacity_shape :
    (∀ z ∈ Set.Ioo (0 : ℝ) 1, 0 < unruhCapacity z) ∧
    AntitoneOn unruhCapacity (Set.Ioo 0 1) ∧
    ConvexOn ℝ (Set.Ioo 0 1) unruhCapacity ∧
    Tendsto unruhCapacity (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) ∧
    Tendsto unruhCapacity (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end
