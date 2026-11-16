-- Prove2me | Theorems.Thm_SubsetConvFPRAS_Supplement_theorem_D_1
-- name    : SubsetConvFPRAS.Supplement.theorem_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:49:48.400328+00:00
-- url     : https://prove2.me/theorems/dcf423f2-35bd-43ba-99a4-1426f1d583d7
-- title:
--   Theorem D.1 — spectral gap $\ge 1/(n(1+\lambda)(1+\lambda(n-1)))$ for the matroid-intersection monomer-dimer Glauber dynamics
-- statement:
--   Let $M,N$ be matroids on a common ground set $U$ with $n=|U|\ge1$, let $\lambda\ge0$, and let $P_\lambda$ be the heat-bath Glauber dynamics of the monomer-dimer law $\mu_\lambda(S)\propto\lambda^{|S|}$ on the common independent sets $\Omega=\mathcal I(M)\cap\mathcal I(N)$, with $L_\lambda=I-P_\lambda$. Then the spectral gap satisfies
--   $$\gamma(L_\lambda)\ge\frac{1}{n\,(1+\lambda)\,(1+\lambda(n-1))},$$
--   that is, for every $f:\Omega\to\mathbb R$,
--   $$\frac{1}{n(1+\lambda)(1+\lambda(n-1))}\operatorname{Var}_{\mu_\lambda}[f]\le\langle f,L_\lambda f\rangle_{\mu_\lambda}.$$
--
--   The bound decays polynomially in $\lambda$ and holds for every pair of matroids, so the matroid-intersection monomer-dimer model has no dynamical phase transition in the fugacity $\lambda$.
--
--   Differences from the source:
--   - encoding: γ(L_λ) ≥ 1/(n(1+λ)(1+λ(n−1))) → the Poincaré inequality c·Var_{μ_λ}[f] ≤ ⟨f, L_λ f⟩_{μ_λ} for every f : Ω → ℝ, with c = 1/(n(1+λ)(1+λ(n−1))); reason: (10)–(11), p.17: the spectral gap is the infimum of the ratio over nonconstant f; on a one-point Ω (λ = 0 or no nonempty common independent set) both forms hold trivially
--   - encoding: L_λ = I − P_λ with the holding probability on the diagonal → the Dirichlet form of the off-diagonal entries of P_λ (glauberKernel, diagonal 0); reason: ⟨f,(I−P_λ)f⟩ depends only on the off-diagonal entries since the rows of P_λ sum to 1
--   - encoding: two matroids M, N on a common ground set U, |U| = n → Mathlib matroids on Fin n with ground set univ (loops allowed); reason: U = Fin n
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Theorem D.1, p.64; (10)–(11), p.17; proof pp.64–65

import Mathlib
import Definitions.Def_SubsetConvFPRAS_ReversibleChain
import Definitions.Def_SubsetConvFPRAS_Supplement_MonomerDimer

open scoped Classical

namespace SubsetConvFPRAS.Supplement

open SubsetConvFPRAS

/-- Chen, Liu, arXiv:2610.06724 (sha256 6c1d68c2…), Theorem D.1, p.64. For every pair of matroids
`M, N` on a common ground set of size `n ≥ 1` and every `λ ≥ 0`, the heat-bath Glauber dynamics `P_λ`
of the monomer-dimer law `μ_λ(S) ∝ λ^|S|` on common independent sets satisfies
`γ(L_λ) ≥ 1/(n(1+λ)(1+λ(n−1)))`, `L_λ = I − P_λ`.

**Formalization Note.** The spectral-gap bound is stated as the Poincaré inequality (11), p.17:
`c · Var_{μ_λ}[f] ≤ ⟨f, L_λ f⟩_{μ_λ}` for every `f`, which by (10) is `γ(L_λ) ≥ c`. The Dirichlet form
`dirichlet` uses only the off-diagonal entries of `P_λ` (`glauberKernel`). Loops are allowed. -/
theorem theorem_D_1 (n : ℕ) (hn : 1 ≤ n) (M N : Matroid (Fin n))
    (hM : M.E = Set.univ) (hN : N.E = Set.univ) (lam : ℝ) (hlam : 0 ≤ lam) :
    HasPoincare (monomerDimerLaw M N lam) (glauberKernel M N lam)
      (1 / ((n : ℝ) * (1 + lam) * (1 + lam * ((n : ℝ) - 1)))) := by sorry

end SubsetConvFPRAS.Supplement
