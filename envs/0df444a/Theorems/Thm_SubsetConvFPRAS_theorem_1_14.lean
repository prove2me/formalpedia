-- Prove2me | Theorems.Thm_SubsetConvFPRAS_theorem_1_14
-- name    : SubsetConvFPRAS.theorem_1_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:20:39.829565+00:00
-- url     : https://prove2.me/theorems/76ce6577-c99b-4434-a5a2-230f83ef59df
-- title:
--   Theorem 1.14 — Main Poincaré inequality for Hadamard products under spectral curvature
-- statement:
--   Let $\mu,\nu:2^U\to\mathbb R_{\ge0}$ have a common nonempty support $\Omega$, connected under single-element additions and deletions, and let $\rho=\mu\odot\nu$. If $\mu$ has $\eta$-spectral curvature and the dual $\nu^*$ has $\kappa$-spectral curvature, where $\eta,\kappa\in\mathbb R$ and $\eta+\kappa>0$, then
--   $$(\eta+\kappa)\operatorname{Var}_\rho[f]\le\langle f,\mathcal Lf\rangle_\rho\qquad\text{for all }f.$$
--
--   This is the paper's main technical theorem: a spectral-gap bound for the natural birth–death chain on $\mu\odot\nu$ from two local, checkable curvature conditions. With $\eta=0$, $\kappa=1$ it gives the Poincaré inequality of Corollary 5.7, and through it the sampler of Corollary 5.6.
--
--   Differences from the source:
--   - encoding: f : Ω → ℝ on the support Ω → f defined on all of 2^U; reason: every term is weighted by ρ, which is 0 off Ω, and moves out of Ω have rate 0, so the values off Ω do not enter
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Theorem 1.14, p.6 (proof p.19)

import Mathlib
import Definitions.Def_SubsetConvFPRAS_ReversibleChain
import Definitions.Def_SubsetConvFPRAS_Hadamard

open scoped Classical

namespace SubsetConvFPRAS

/-- Chen, Liu, arXiv:2610.06724 (sha256 6c1d68c2…), Theorem 1.14 (Main Poincaré Inequality), p.6. If `μ, ν`
have a common nonempty connected support, `μ` has `η`-spectral curvature, `ν*` has `κ`-spectral curvature
and `η + κ > 0`, then `(η + κ) Var_ρ[f] ≤ ⟨f, 𝓛 f⟩_ρ` for `ρ = μ ⊙ ν`.

**Formalization Note.** A function on `Ω` is given as a function on `2^U`: every term is weighted by `ρ`,
and moves out of `Ω` have rate `0`, so the values off `Ω` do not matter. -/
theorem theorem_1_14 {U : Type} [Fintype U] [DecidableEq U] (μ ν : Finset U → ℝ)
    (hμ : ∀ S, 0 ≤ μ S) (hν : ∀ S, 0 ≤ ν S) (hsupp : ∀ S, 0 < μ S ↔ 0 < ν S) (hne : ∃ S, 0 < μ S)
    (hconn : SupportConnected μ) (η κ : ℝ) (hcμ : HasCurv μ η) (hcν : HasCurv (dual ν) κ)
    (hηκ : 0 < η + κ) (f : Finset U → ℝ) :
    (η + κ) * variance (hadamard μ ν) f ≤ innerPi (hadamard μ ν) f (hadLapl μ ν f) := by sorry

end SubsetConvFPRAS
