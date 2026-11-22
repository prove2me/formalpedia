-- Prove2me | Theorems.Thm_SeparateContinuity_continuous_of_separately_seqContinuous
-- name    : SeparateContinuity.continuous_of_separately_seqContinuous
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:05.709707+00:00
-- url     : https://prove2.me/theorems/b97cc907-7c6d-4598-a35c-1f7b46575e8b
-- title:
--   A separately (sequentially) continuous bilinear map on (F-space) × (first countable TVS) is jointly continuous
-- statement:
--   **Joint continuity of separately continuous bilinear maps on metrizable spaces.**
--
--   Let $\mathbb k$ be $\mathbb R$ or $\mathbb C$, let $E$, $F$, $G$ be topological vector spaces over $\mathbb k$. Assume that $E$ is completely metrizable (an $F$-space, e.g. a Fréchet space) and that $F$ is first countable (e.g. metrizable). Let
--   $$A:E\times F\to G$$
--   be a bilinear map which is separately sequentially continuous (in particular: any separately continuous bilinear map), i.e. $y\mapsto A(x,y)$ is sequentially continuous for every $x\in E$ and $x\mapsto A(x,y)$ is sequentially continuous for every $y\in F$.
--
--   Then $A$ is **jointly continuous** on $E\times F$.
--
--   The target $G$ is an arbitrary topological vector space. This is the form in which Proposition C.2.3.11 of the paper is applied ("when sequences are sufficient to probe the topologies of $E$ and $F$"): for Fréchet spaces $E$, $F$ it shows that every separately continuous bilinear map into any locally convex space is continuous, which is what identifies $E\otimes_\iota F$ with $E\otimes_\pi F$.
--
--   **Formalization Note.** Same encoding as for the sequential statement: `TopologicalSpace.IsCompletelyMetrizableSpace E` for the $F$-space hypothesis and a bilinear map `A : E →ₗ[𝕜] F →ₗ[𝕜] G`. The hypothesis on $F$ is `FirstCountableTopology F`, which for a Hausdorff topological vector space is the same as metrizability. The conclusion is `Continuous (fun p : E × F => A p.1 p.2)`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 681–682, Proposition C.2.3.11 (proved there from the uniform boundedness principle [H. H. Schaefer with M. P. Wolff, Topological Vector Spaces, 2nd ed., Springer, Ch. III, 4.2]; for similar arguments the paper refers to N. Bourbaki, Topological Vector Spaces, Ch. III, §5, no. 2, Prop. 2, p. III.29 and Cor. 1, p. III.30)

import Mathlib

open Topology Filter
set_option autoImplicit false

namespace SeparateContinuity

theorem continuous_of_separately_seqContinuous {𝕜 E F G : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [TopologicalSpace.IsCompletelyMetrizableSpace E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜 F] [FirstCountableTopology F]
    [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [ContinuousSMul 𝕜 G]
    (A : E →ₗ[𝕜] F →ₗ[𝕜] G)
    (h₁ : ∀ x : E, SeqContinuous (fun y : F => A x y))
    (h₂ : ∀ y : F, SeqContinuous (fun x : E => A x y)) :
    Continuous (fun p : E × F => A p.1 p.2) := by sorry

end SeparateContinuity
