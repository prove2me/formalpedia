-- Prove2me | Theorems.Thm_VectorValuedHolomorphy_continuousOn_of_forall_strongDual_differentiableOn
-- name    : VectorValuedHolomorphy.continuousOn_of_forall_strongDual_differentiableOn
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:49:11.973797+00:00
-- url     : https://prove2.me/theorems/45d5e2c1-8684-4831-ae41-4f06bc44fad7
-- title:
--   A weakly holomorphic function with values in a Hausdorff locally convex space is continuous (no completeness needed)
-- statement:
--   **Weakly holomorphic functions are continuous for the original topology.**
--
--   Let $E$ be a Hausdorff locally convex topological vector space over $\mathbb C$ with continuous dual $E'$; no completeness is assumed. Let $U\subset\mathbb C$ be open and let $f:U\to E$ be *weakly holomorphic*: for every $\varphi\in E'$ the scalar function $z\mapsto\langle f(z),\varphi\rangle$ is holomorphic on $U$.
--
--   Then $f$ is continuous on $U$ for the given topology of $E$ (not merely for the weak topology $\sigma(E,E')$):
--   $$\langle f(\cdot),\varphi\rangle\ \text{holomorphic on }U\ \text{for all }\varphi\in E'\ \Longrightarrow\ f:U\to E\ \text{continuous}.$$
--
--   This is the first step of Grothendieck's theorem on weak and strong holomorphy, and the only step that does not use completeness. Continuity is what makes the Cauchy integrals of $f$ available as vector-valued integrals of a continuous function on a compact contour. The paper recalls this step in Remark C.5.2.7.
--
--   **Formalization Note.** `E` is a complex topological vector space (`[TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]`), locally convex in the sense of Mathlib's `PolynormableSpace ℂ E`, and Hausdorff; $E'$ is `StrongDual ℂ E`. Functions are total maps `ℂ → E` and the conclusion is `ContinuousOn f U`. **Deviation from the source.** Remark C.5.2.7 says in (1) that continuity "has to be shown directly and without the aid of quasi-completeness" and in (2) that weak holomorphy implies continuity "in the presence of quasi-completeness"; the statement formalized is the sharp classical one, without any completeness hypothesis. The open set is arbitrary (the source takes a domain).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 739, Remark C.5.2.7(1)-(2) (on Theorem C.5.2.6); classical reference: A. Grothendieck, Sur certains espaces de fonctions holomorphes. I, J. reine angew. Math. 192 (1953), pp. 35-64, p. 38 (the argument for continuity)

import Mathlib

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace VectorValuedHolomorphy

theorem continuousOn_of_forall_strongDual_differentiableOn {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [T2Space E] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → E} (hf : ∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (fun z => ℓ (f z)) U) :
    ContinuousOn f U := by sorry

end VectorValuedHolomorphy
