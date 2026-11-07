-- Prove2me | Theorems.Thm_SubsetConvFPRAS_corollary_5_7
-- name    : SubsetConvFPRAS.corollary_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:21:31.345684+00:00
-- url     : https://prove2.me/theorems/bac4b5b0-9c49-4044-b35c-e6025f9d12f3
-- title:
--   Corollary 5.7 — Poincaré inequality with constant $1$ for the independent-set pair law $\hat\pi_{t,\lambda z}$
-- statement:
--   Assume the standing hypotheses of §5 ($\mu,\nu\ge0$ supported on $\binom Ua,\binom Ub$, $a+b=n\ge1$, $g_\mu,g_\nu$ log-concave). Let $t\in(0,1]^U$, $z\in\mathbb R^U_{>0}$ and $\lambda>0$. On the ground set $U\sqcup U$ let $w_\lambda(S,T)=\hat\mu_{\lambda z}(S)\hat\nu_{\lambda z}(T)$ and let $\psi_t(S,T)=t^{S\cap T}$, restricted to $\operatorname{supp}w_\lambda$. With $\hat\pi_{t,\lambda z}=w_\lambda\odot\psi_t$ and $\mathcal L$ the Laplacian (3) for these two factors, with rates $\hat q_\lambda$,
--   $$\operatorname{Var}_{\hat\pi_{t,\lambda z}}[F]\le\mathcal E_{\hat q_\lambda}(F,F)=\langle F,\mathcal LF\rangle_{\hat\pi_{t,\lambda z}}\qquad\text{for every }F.$$
--
--   The bound is uniform in $\lambda$; letting $\lambda\to\infty$ in the induced chain gives the exchange chain of Lemma 5.5.
--
--   Differences from the source:
--   - encoding: F : supp π̂_{t,λz} → ℝ → F defined on all subsets of U ⊔ U; reason: every term is weighted by π̂, which is 0 off the support, and moves out of the support have rate 0
--   - encoding: pairs (S,T) ∈ 2^U × 2^U and copies (u,1), (u,2) → subsets of U ⊔ U, with S the left part and T the right part; reason: the bijection of p.22, which lets Theorem 1.14 apply on the ground set U ⊔ U
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), (21) and Corollary 5.7, p.22

import Mathlib
import Definitions.Def_SubsetConvFPRAS_PairLaws

open scoped Classical

namespace SubsetConvFPRAS

/-- Chen, Liu, arXiv:2610.06724 (sha256 6c1d68c2…), Corollary 5.7, p.22, with (21). On the factors `w_λ`,
`ψ_t` (on the ground set `U ⊕ U`), the law `π̂_{t,λz} = w_λ ⊙ ψ_t` satisfies
`Var[F] ≤ E_{q̂_λ}(F,F) = ⟨F, 𝓛 F⟩`.

**Formalization Note.** The standing hypotheses of §5 are `IsHomogeneousPair`. `F` is a function on all of
`2^{U ⊕ U}`; the values off the support do not matter. -/
theorem corollary_5_7 {U : Type} [Fintype U] [DecidableEq U] (a b : ℕ) (μ ν : Finset U → ℝ)
    (h : IsHomogeneousPair a b μ ν) (t z : U → ℝ) (ht : ∀ u, 0 < t u ∧ t u ≤ 1) (hz : ∀ u, 0 < z u)
    (lam : ℝ) (hlam : 0 < lam) (F : Finset (U ⊕ U) → ℝ) :
    let w := wLam μ ν lam z
    let ψ := psiRestricted t w
    variance (hadamard w ψ) F ≤ dirichlet (hadamard w ψ) (hadRate w ψ) F F ∧
      dirichlet (hadamard w ψ) (hadRate w ψ) F F = innerPi (hadamard w ψ) F (hadLapl w ψ F) := by sorry

end SubsetConvFPRAS
