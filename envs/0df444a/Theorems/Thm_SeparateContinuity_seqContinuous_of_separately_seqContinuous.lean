-- Prove2me | Theorems.Thm_SeparateContinuity_seqContinuous_of_separately_seqContinuous
-- name    : SeparateContinuity.seqContinuous_of_separately_seqContinuous
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:07.77646+00:00
-- url     : https://prove2.me/theorems/63dedbb3-2061-496a-bfcb-980f6d49c70b
-- title:
--   A separately sequentially continuous bilinear map on (F-space) × (topological vector space) is sequentially continuous
-- statement:
--   **Sequential continuity of separately sequentially continuous bilinear maps.**
--
--   Let $\mathbb k$ be $\mathbb R$ or $\mathbb C$, let $E$, $F$, $G$ be topological vector spaces over $\mathbb k$, and assume that $E$ is completely metrizable (an $F$-space; in particular any Fréchet space). Let
--   $$A:E\times F\to G$$
--   be a bilinear map which is **separately sequentially continuous**: for every $x\in E$ the map $y\mapsto A(x,y)$ is sequentially continuous on $F$, and for every $y\in F$ the map $x\mapsto A(x,y)$ is sequentially continuous on $E$.
--
--   Then $A$ is **sequentially continuous**: whenever $x_m\to x$ in $E$ and $y_m\to y$ in $F$,
--   $$A(x_m,y_m)\longrightarrow A(x,y)\quad\text{in }G.$$
--
--   No assumption is made on $F$ and $G$ beyond being topological vector spaces (they need not be metrizable, locally convex or Hausdorff). The result is the standard consequence of the Banach–Steinhaus theorem for the Baire space $E$; in the paper it is the engine behind the equality of the inductive and projective tensor topologies on Fréchet spaces (Corollary C.2.3.12) and is used whenever continuity of a map out of a projective tensor product has to be checked on sequences.
--
--   **Formalization Note.** The source states the result for Hausdorff locally convex spaces over $\mathbb C$ with $E$ Fréchet; the statement here is the same theorem in its natural generality (its proof, the one given in the source, uses only that $E$ is a completely metrizable topological vector space), so the source's statement is the special case of locally convex $E,F,G$. "$E$ is an $F$-space" is expressed by `TopologicalSpace.IsCompletelyMetrizableSpace E` together with the topological vector space instances; $A$ is a $\mathbb k$-bilinear map `E →ₗ[𝕜] F →ₗ[𝕜] G`; the conclusion is `SeqContinuous` of the uncurried map on the product $E\times F$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 681–682, Proposition C.2.3.11 (proved there from the uniform boundedness principle [H. H. Schaefer with M. P. Wolff, Topological Vector Spaces, 2nd ed., Springer, Ch. III, 4.2]; for similar arguments the paper refers to N. Bourbaki, Topological Vector Spaces, Ch. III, §5, no. 2, Prop. 2, p. III.29 and Cor. 1, p. III.30)

import Mathlib

open Topology Filter
set_option autoImplicit false

namespace SeparateContinuity

theorem seqContinuous_of_separately_seqContinuous {𝕜 E F G : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [TopologicalSpace.IsCompletelyMetrizableSpace E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜 F]
    [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [ContinuousSMul 𝕜 G]
    (A : E →ₗ[𝕜] F →ₗ[𝕜] G)
    (h₁ : ∀ x : E, SeqContinuous (fun y : F => A x y))
    (h₂ : ∀ y : F, SeqContinuous (fun x : E => A x y)) :
    SeqContinuous (fun p : E × F => A p.1 p.2) := by sorry

end SeparateContinuity
