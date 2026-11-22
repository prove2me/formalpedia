-- Prove2me | Theorems.Thm_VectorValuedHolomorphy_quasiCompleteSpace_compactlySupported
-- name    : VectorValuedHolomorphy.quasiCompleteSpace_compactlySupported
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:25:07.07987+00:00
-- url     : https://prove2.me/theorems/dbb7bd4e-eaa2-4938-a69b-0fe25c83c056
-- title:
--   Lemma C.5.1.3(3) — for $X$ paracompact and $E$ quasi-complete, $C_c(X,E)$ with the inductive limit topology is quasi-complete
-- statement:
--   **Quasi-completeness of $C_c(X,E)$ (Lemma C.5.1.3(3)).** Let $X$ be a paracompact locally compact Hausdorff space and $E$ a quasi-complete Hausdorff locally convex space over $\mathbb k\in\{\mathbb R,\mathbb C\}$. Then the space $C_c(X,E)$ of continuous compactly supported functions $X\to E$, with the locally convex inductive limit topology of the subspaces $C(X,K;E)$ ($K\subset X$ compact, topology of uniform convergence), is quasi-complete: every closed bounded subset of $C_c(X,E)$ is complete.
--
--   Since a bounded subset of $C_c(X,E)$ lies in a single $C(X,K;E)$ when $X$ is paracompact, this reduces to the quasi-completeness of $C(X,K;E)$ for uniform convergence. Quasi-completeness is the standing hypothesis of the paper on spaces of values (it makes continuous compactly supported functions Pettis integrable and weakly holomorphic functions holomorphic), and this statement shows that it is inherited by spaces of vector-valued test functions.
--
--   **Formalization Note.** The conclusion is `@QuasiCompleteSpace 𝕜 C_c(X, E) _ (compactlySupportedUniformSpace 𝕜 X E) _ _`, where `compactlySupportedUniformSpace 𝕜 X E` (definition file) is the uniform structure of the topological additive group $C_c(X,E)$ with the inductive limit topology; `QuasiCompleteSpace` is Mathlib's class (closed von Neumann bounded sets are complete). For `E`, "quasi-complete Hausdorff locally convex space" is `[UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E] [QuasiCompleteSpace 𝕜 E]` (the topology is defined by a family of seminorms; closed von Neumann bounded sets are complete); paracompactness is `[ParacompactSpace X]`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 721, Lemma C.5.1.3(3) (proof on p. 722); classical reference: N. Bourbaki, Elements of Mathematics, Integration I, Springer, Ch. III, §1, p. III.4, Corollary (as cited by the paper)

import Mathlib
import Definitions.Def_VectorValuedHolomorphy_CompactlySupportedInductiveLimit

open Filter Topology
open scoped CompactlySupported

set_option autoImplicit false

namespace VectorValuedHolomorphy

/-- If `X` is paracompact (locally compact Hausdorff) and `E` is a quasi-complete Hausdorff
locally convex space, then `C_c(X, E)` with the locally convex inductive limit topology is
quasi-complete. -/
theorem quasiCompleteSpace_compactlySupported (𝕜 : Type*) [RCLike 𝕜] (X : Type*)
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [ParacompactSpace X] (E : Type*)
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E] [QuasiCompleteSpace 𝕜 E] :
    @QuasiCompleteSpace 𝕜 C_c(X, E) _ (compactlySupportedUniformSpace 𝕜 X E) _ _ := by sorry

end VectorValuedHolomorphy
