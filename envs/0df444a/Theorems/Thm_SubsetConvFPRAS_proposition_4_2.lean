-- Prove2me | Theorems.Thm_SubsetConvFPRAS_proposition_4_2
-- name    : SubsetConvFPRAS.proposition_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:20:44.999573+00:00
-- url     : https://prove2.me/theorems/2724d402-9f06-415a-8b1b-4aca1b287d13
-- title:
--   Proposition 4.2 — the Bochner identity for $\mathcal L$
-- statement:
--   Assume the hypotheses of Theorem 1.14: $\mu,\nu\ge0$ have a common nonempty support $\Omega$ connected under single-element additions and deletions, $\mu$ has $\eta$-spectral curvature, $\nu^*$ has $\kappa$-spectral curvature, and $\eta+\kappa>0$. Let $\rho=\mu\odot\nu$, $Z=\sum_S\mu(S)\nu(S)$ and $\mathcal L$ the Laplacian (3). Then for every $f:2^U\to\mathbb R$,
--   $$\bigl\langle f,(\mathcal L^2-(\eta+\kappa)\mathcal L)f\bigr\rangle_\rho=\sum_{S\in\Omega}\rho(S)\,(\nabla^+f)(S)^\top A^{\mu,\eta}_S(\nabla^+f)(S)+\sum_{S\in\Omega}\rho(S)\,(\nabla^-f)(S)^\top D^{\nu,\kappa}_S(\nabla^-f)(S)+\frac1Z\sum_{S\in\Omega}\ \sum_{\substack{u,v\notin S,\ u\ne v\\ S+u+v\in\Omega}}\mu(S+u+v)\,\nu(S)\,(\Delta_{uv}f)(S)^2,$$
--   where $(\Delta_{uv}f)(S)=f(S+u+v)-f(S+u-v)-f(S-u+v)+f(S-u-v)$ and $D^{\nu,\kappa}_S=A^{\nu^*,\kappa}_{U\setminus S}$.
--
--   Since the curvature terms are nonnegative under the hypotheses, this identity gives $\langle\mathcal Lf,\mathcal Lf\rangle_\rho\ge(\eta+\kappa)\langle f,\mathcal Lf\rangle_\rho$, the input of Proposition 2.1 in the proof of Theorem 1.14.
--
--   **Formalization Note** The last sum runs over ordered pairs $(u,v)$, as the page's "$u,v\notin S$: $u\neq v$" does (checked numerically at planning). The sums over $\Omega$ are sums over all $S$ weighted by $\rho$, which vanishes off $\Omega$.
--
--   Differences from the source:
--   - encoding: sums over S ∈ Ω → sums over all S ⊆ U, weighted by ρ(S) (0 off Ω) or guarded by μ(S) > 0; reason: same value
--   - encoding: signed rates r_u(S) acting on f(S+u) − f(S−u) → nonnegative rates |r_u(S)| acting on f(S) − f(S △ u); reason: the same operator 𝓛
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Proposition 4.2, p.19 (proof pp.19–20)

import Mathlib
import Definitions.Def_SubsetConvFPRAS_ReversibleChain
import Definitions.Def_SubsetConvFPRAS_Hadamard

open scoped Classical

namespace SubsetConvFPRAS

/-- Chen, Liu, arXiv:2610.06724 (sha256 6c1d68c2…), Proposition 4.2, p.19. The Bochner identity for `𝓛`,
under the hypotheses of Theorem 1.14.

**Formalization Note.** `f` is any function on `2^U`, as on the page. The last sum runs over ordered pairs
`(u,v)`, as the page's `u, v ∉ S : u ≠ v`. -/
theorem proposition_4_2 {U : Type} [Fintype U] [DecidableEq U] (μ ν : Finset U → ℝ)
    (hμ : ∀ S, 0 ≤ μ S) (hν : ∀ S, 0 ≤ ν S) (hsupp : ∀ S, 0 < μ S ↔ 0 < ν S) (hne : ∃ S, 0 < μ S)
    (hconn : SupportConnected μ) (η κ : ℝ) (hcμ : HasCurv μ η) (hcν : HasCurv (dual ν) κ)
    (hηκ : 0 < η + κ) (f : Finset U → ℝ) :
    innerPi (hadamard μ ν) f
        (fun S => hadLapl μ ν (hadLapl μ ν f) S - (η + κ) * hadLapl μ ν f S) =
      (∑ S, hadamard μ ν S *
          (gradPlus f S ⬝ᵥ ((curvMatrix μ η S).mulVec (gradPlus f S)))) +
      (∑ S, hadamard μ ν S *
          (gradMinus f S ⬝ᵥ ((downCurvMatrix ν κ S).mulVec (gradMinus f S)))) +
      (1 / ∑ T, μ T * ν T) * ∑ S, ∑ u, ∑ v,
        if 0 < μ S ∧ u ∉ S ∧ v ∉ S ∧ u ≠ v ∧ 0 < μ (insert u (insert v S)) then
          μ (insert u (insert v S)) * ν S * (mixedDiff u v f S) ^ 2
        else 0 := by sorry

end SubsetConvFPRAS
