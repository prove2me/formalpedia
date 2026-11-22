-- Prove2me | Theorems.Thm_VectorValuedHolomorphy_existsUnique_hasResidueAt
-- name    : VectorValuedHolomorphy.existsUnique_hasResidueAt
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:40.202409+00:00
-- url     : https://prove2.me/theorems/3ac86035-94fd-416d-ac25-dc618b5fac3c
-- title:
--   Existence and uniqueness of the residue of a meromorphic function with values in a quasi-complete locally convex space
-- statement:
--   **The residue of a vector-valued meromorphic function is well defined.**
--
--   Let $E$ be a quasi-complete Hausdorff locally convex topological vector space over $\mathbb C$ and let $f$ be an $E$-valued function meromorphic at $z_0\in\mathbb C$: some $(z-z_0)^n f(z)$, $n\ge 0$, extends holomorphically across $z_0$.
--
--   Then $f$ has a principal part at $z_0$ with coefficients in $E$: there are an integer $m\ge 0$, vectors $a_0,\dots,a_m\in E$ and a function $h$ holomorphic on a neighbourhood of $z_0$ such that
--   $$f(z)=\sum_{j=0}^{m}\frac{a_j}{(z-z_0)^{j+1}}+h(z)\qquad\text{for }z\ne z_0\text{ close to }z_0 ,$$
--   and the coefficient $a_0$ of $(z-z_0)^{-1}$ is the same for all such decompositions. In other words there is exactly one vector
--   $$\operatorname{Res}_{z_0}(f)=a_{-1}(z_0,f)\in E$$
--   which is the residue of $f$ at $z_0$.
--
--   The paper defines $\operatorname{Res}_{\xi}(f):=a_{-1}(\xi,f)$ for meromorphic $E$-valued functions, formula (C.5.3.5), and uses the residue operators in its vector-valued Residue Theorem; this statement is the well-definedness of that operator.
--
--   **Formalization Note.** `E` is a complex vector space with a uniform structure making it a uniform additive group (`[UniformSpace E] [IsUniformAddGroup E]`), with continuous scalar multiplication, locally convex in the sense of Mathlib's `PolynormableSpace ℂ E` (the topology is defined by a family of seminorms), Hausdorff (`T2Space`) and quasi-complete (`QuasiCompleteSpace ℂ E`: closed von Neumann bounded sets are complete). The continuous dual $E'$ is `StrongDual ℂ E`. `MeromorphicAt` and `HasResidueAt` are the predicates of the definition file `VectorValuedHolomorphy_Meromorphic`; `HasResidueAt f z₀ r` is the existence of a decomposition as above with `a 0 = r`. The conclusion is `∃! r : E, HasResidueAt f z₀ r`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 740, formula (C.5.3.5) and Lemma C.5.3.3 (the residue operators on meromorphic E-valued functions), with Definition C.5.3.1 (p. 739)

import Mathlib
import Definitions.Def_VectorValuedHolomorphy_Meromorphic

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace VectorValuedHolomorphy

theorem existsUnique_hasResidueAt {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] [QuasiCompleteSpace ℂ E] {f : ℂ → E} {z₀ : ℂ} (hf : MeromorphicAt f z₀) :
    ∃! r : E, HasResidueAt f z₀ r := by sorry

end VectorValuedHolomorphy
