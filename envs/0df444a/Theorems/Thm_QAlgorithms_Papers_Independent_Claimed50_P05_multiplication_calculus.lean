-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_multiplication_calculus
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.multiplication_calculus
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:04:50.700573+00:00
-- url     : https://prove2.me/theorems/738b1ff0-1e64-4e74-a250-ae49388f8f62
-- title:
--   Theorem 2.9
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be any measure space and let $k\in\{\mathbb R,\mathbb C\}$. For $a\in M(\Omega)$ define a graph on $L^2(\mu;k)$ by
--
--   $$(u,v)\in M_a\quad\Longleftrightarrow\quad v=a u\quad\mu\text{-almost everywhere}.$$
--
--   Equivalently, $\operatorname{dom}M_a=\{u\in L^2:a u\in L^2\}$ and $M_a u=a u$ as equivalence classes. Then $a\mapsto M_a$ is a measurable functional calculus. No semifiniteness or sigma-finiteness is assumed.
--
--   This constructs the multiplication model on an arbitrary measure space.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 13, Theorem 2.9

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05

universe u v w

variable {k : Type*} [RCLike k]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

/-- Theorem 2.9, PDF p.13: the L2 multiplication calculus, with no finiteness assumption. -/
theorem multiplication_calculus (mu : Measure X) : Calculus (multiplication (k := k) mu) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
