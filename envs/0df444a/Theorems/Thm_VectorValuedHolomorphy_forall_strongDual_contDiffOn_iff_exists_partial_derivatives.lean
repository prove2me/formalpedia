-- Prove2me | Theorems.Thm_VectorValuedHolomorphy_forall_strongDual_contDiffOn_iff_exists_partial_derivatives
-- name    : VectorValuedHolomorphy.forall_strongDual_contDiffOn_iff_exists_partial_derivatives
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:49:19.37697+00:00
-- url     : https://prove2.me/theorems/c2125abf-c593-4f34-9930-916bbea37791
-- title:
--   Grothendieck-Schwartz: a weakly $C^\infty$ function on an open subset of $\mathbb R^d$ with values in a quasi-complete locally convex space is $C^\infty$
-- statement:
--   **Weak smoothness equals smoothness for functions with values in a quasi-complete space (Grothendieck, Schwartz).**
--
--   Let $E$ be a quasi-complete Hausdorff locally convex topological vector space with continuous dual $E'$, let $\Omega\subset\mathbb R^d$ be open and let $f:\Omega\to E$ be a function. Say that $f$ is *infinitely differentiable* (smooth) if all its iterated partial derivatives exist in $E$ and are continuous: for every finite sequence of indices $i_1,\dots,i_m\in\{1,\dots,d\}$ the function
--   $$\partial_{i_m}\cdots\partial_{i_1}f:\Omega\to E$$
--   is defined, each partial derivative being a limit of difference quotients
--   $$\partial_i g(x)=\lim_{t\to 0}\frac{g(x+te_i)-g(x)}{t}$$
--   in the topology of $E$, where $e_i$ is the $i$-th standard basis vector of $\mathbb R^d$, and is continuous on $\Omega$.
--
--   The theorem states that $f$ is smooth if and only if it is weakly smooth:
--   $$f\in C^\infty(\Omega,E)\iff\ \langle f(\cdot),\varphi\rangle\in C^\infty(\Omega)\ \text{for every }\varphi\in E' .$$
--
--   The implication $\Leftarrow$ is the content: scalar smoothness of all the functions $\langle f,\varphi\rangle$ forces the difference quotients of $f$ and of its derivatives to converge in $E$ itself; this requires a completeness assumption, and quasi-completeness suffices. The result reconciles the "weak" definition of vector-valued smooth functions (Schwartz) with the "strong" one (Trèves); the paper uses it to speak unambiguously of smooth and Schwartz functions with values in quasi-complete spaces.
--
--   **Formalization Note.** The scalar field of the formal statement is $\mathbb R$: `E` is a real locally convex space (`PolynormableSpace ℝ E`, with `[UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [QuasiCompleteSpace ℝ E]`) and `ℓ` ranges over `StrongDual ℝ E`. The paper works with complex spaces and complex functionals; a complex locally convex space is a real one with the same bounded sets, and its real continuous functionals are the real parts of the complex ones, so the real statement contains the complex one. Weak smoothness is `∀ ℓ n, ContDiffOn ℝ n (fun x => ℓ (f x)) Ω` with `n : ℕ` (all finite orders). Because Mathlib's `ContDiffOn` needs a normed target, smoothness of `f` is spelled out: there is a family `D : List (Fin d) → ((Fin d → ℝ) → E)` with `D [] = f`, every `D I` continuous on `Ω`, and `D (i :: I) x` the derivative at `t = 0` of `t ↦ D I (x + t • eᵢ)` for every `x ∈ Ω` (`HasDerivAt`, which for a topological vector space target means convergence of difference quotients in `E`); so `D [i₁, …, i_m] = ∂_{i₁}⋯∂_{i_m} f`. The domain is `Fin d → ℝ` with basis vectors `Pi.single i 1`. Only the case of a real variable ($k=\mathbb R$ in the source) is covered; for one complex variable the corresponding statement is Grothendieck's holomorphy criterion. **Deviation from the source.** Definition C.5.1.23 of the paper contains an additional order-$0$ clause (C.5.1.43): the quotients $(f(\xi')-f(\xi))/|\xi'-\xi|$ with $\xi\ne\xi'$ and $|\xi'-\xi|\le 1$ are required to lie in a bounded subset of $E$ ("Lipschitz-continuity": one bounded set for all such pairs), and "infinitely differentiable" means "continuously differentiable $m$ times for every $m\ge 0$". This global bound fails already for the smooth function $x\mapsto x^2$ on $\mathbb R$ (with $E=\mathbb C$), so Corollary C.5.1.25 is not correct as printed. The formal statement uses the classical notion of smoothness (all iterated partial derivatives exist in $E$ and are continuous), for which the equivalence is the classical theorem of Grothendieck and Schwartz; the paper itself states that its Definition C.5.1.23 is meant to be the same notion as that of Trèves.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 734, Corollary C.5.1.25 (with Definition C.5.1.23, p. 733, and Theorem C.5.1.24, p. 734); classical references given there: A. Grothendieck, Sur certains espaces de fonctions holomorphes. I, J. reine angew. Math. 192 (1953), pp. 35-64, §2, footnote 4, p. 39, and L. Schwartz, Espaces de fonctions différentiables à valeurs vectorielles, vol. 4 (1954), pp. 88-148, Appendice, Lemme II, p. 146

import Mathlib

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace VectorValuedHolomorphy

theorem forall_strongDual_contDiffOn_iff_exists_partial_derivatives {E : Type*}
    [AddCommGroup E] [Module ℝ E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℝ E]
    [PolynormableSpace ℝ E] [T2Space E] [QuasiCompleteSpace ℝ E] {d : ℕ}
    {Ω : Set (Fin d → ℝ)} (hΩ : IsOpen Ω) (f : (Fin d → ℝ) → E) :
    (∀ (ℓ : StrongDual ℝ E) (n : ℕ), ContDiffOn ℝ n (fun x => ℓ (f x)) Ω) ↔
      ∃ D : List (Fin d) → (Fin d → ℝ) → E, D [] = f ∧ (∀ I, ContinuousOn (D I) Ω) ∧
        ∀ (I : List (Fin d)) (i : Fin d), ∀ x ∈ Ω,
          HasDerivAt (fun t : ℝ => D I (x + t • Pi.single i (1 : ℝ))) (D (i :: I) x) 0 := by
  sorry

end VectorValuedHolomorphy
