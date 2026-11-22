-- Prove2me | Theorems.Thm_SchauderBasis_exists_schauderBasis_of_existsUnique_hasSum
-- name    : SchauderBasis.exists_schauderBasis_of_existsUnique_hasSum
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:00:47.265832+00:00
-- url     : https://prove2.me/theorems/e31ff80e-9404-413b-8204-8ebe8b39c276
-- title:
--   Banach's basis theorem: in a Banach space a sequence giving unique series expansions is a Schauder basis (coefficient functionals are continuous)
-- statement:
--   **Banach's basis theorem (automatic continuity of the coefficient functionals).** Let $X$ be a Banach space over $\mathbb K=\mathbb R$ or $\mathbb C$, and let $(e_n)_{n\ge0}$ be a sequence in $X$ such that every $x\in X$ has a **unique** expansion
--   $$x=\sum_{n=0}^{\infty}c_n\,e_n,\qquad\text{i.e. }\ \Big\|x-\sum_{n<N}c_ne_n\Big\|\xrightarrow[N\to\infty]{}0,$$
--   with scalars $c_n=c_n(x)\in\mathbb K$. Then each coefficient functional $x\mapsto c_n(x)$ is a continuous linear functional on $X$; hence $(e_n)$ is a Schauder basis of $X$: there are $e_n^*\in X'$ with $e_n^*(e_m)=\delta_{n,m}$ and $x=\sum_n e_n^*(x)e_n$ for all $x$.
--
--   The paper (p. 157, before and in Definition 4.1.1.1) distinguishes *topological bases* (series expansions with possibly discontinuous coefficient functionals) from *Schauder bases* (continuous coefficient functionals). For the classical notion of topological basis (every vector has a unique expansion), the two notions coincide in Banach spaces, and more generally in Fréchet spaces (theorem `MasulloGRH.frechet_isSchauderBasis_of_existsUnique_expansion`); this is what allows one to use the uniform bound on the partial-sum projections (basis constant) for every such basis of a Banach space.
--
--   **Deviation from the source.** The paper's Definition 4.1.1.1(1) does not ask for uniqueness: it calls $(x_m)$ a topological basis of $E$ as soon as there are merely algebraic linear functionals $f_m\in E^*$ with $f_m(x_n)=\delta_{m,n}$ and $u=\sum_m f_m(u)x_m$ for all $u$. With that literal definition a topological basis need not be a Schauder basis, even in a Hilbert space: in $\ell^2$, with unit vectors $(\varepsilon_k)_{k\ge1}$, take $x_0=\sum_{k\ge1}k^{-1}\varepsilon_k$, $x_k=\varepsilon_k$ $(k\ge1)$, a (necessarily discontinuous) linear functional $f_0$ with $f_0(x_0)=1$ and $f_0(\varepsilon_k)=0$ for all $k\ge1$, and $f_k(u)=u_k-k^{-1}f_0(u)$, where $u_k$ denotes the $k$-th coordinate of $u\in\ell^2$. The statement here uses the classical notion (every vector has a *unique* expansion), for which the coefficient functionals are automatically continuous.
--
--   **Formalization Note.** Mathlib's `SchauderBasis 𝕜 X` bundles the basis vectors, continuous coordinate functionals (`StrongDual 𝕜 X`), biorthogonality, and convergence of the partial sums over `Finset.range N` (`SummationFilter.conditional ℕ`); the hypothesis uses the same summation filter. The conclusion asserts that a `SchauderBasis` with basis vectors exactly `e` exists; its coordinate functionals are then necessarily the unique coefficients. Uniqueness of the expansion is the classical hypothesis (Banach's definition of a basis) and cannot be dropped (see the deviation remark).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 157, Definition 4.1.1.1 and the preceding paragraph (topological bases versus Schauder bases; the paper refers to H. Jarchow, Locally Convex Spaces, Teubner, 1981, Part II, Ch. 14, §14.2, p. 292, for these notions)

import Mathlib

open Filter Topology MeasureTheory AddCircle ENNReal

set_option autoImplicit false

namespace SchauderBasis

theorem exists_schauderBasis_of_existsUnique_hasSum
    {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [CompleteSpace X] (e : ℕ → X)
    (he : ∀ x : X, ∃! c : ℕ → 𝕜,
      HasSum (fun n => c n • e n) x (SummationFilter.conditional ℕ)) :
    ∃ b : SchauderBasis 𝕜 X, b.basis = e := by sorry

end SchauderBasis
