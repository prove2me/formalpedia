-- Prove2me | Theorems.Thm_SPOBounds_Natarajan_Supplement_linear_rademacher_lambda_bound
-- name    : SPOBounds.Natarajan.Supplement.linear_rademacher_lambda_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:41:22.356262+00:00
-- url     : https://prove2.me/theorems/0df6424d-afc0-4b3f-b6e3-aab5ee6663b2
-- title:
--   Proof of Theorem 6 (App. C.2) — $\mathbb E\sup_{B\in\mathcal B}\langle B,\Theta\rangle\le\beta^2/\lambda+\lambda\Omega^2/(2\alpha n)$ for every $\lambda>0$
-- statement:
--   Let $\|\cdot\|$ be a norm on the space $\mathbb R^{d\times p}$ of real matrices and $\|\cdot\|_*$ its dual norm with respect to the trace pairing $\langle B,A\rangle=\sum_{i,j}B_{ij}A_{ij}$. Let $\mathcal S\subseteq\mathbb R^{d\times p}$ be closed and convex, and let $F:\mathcal S\to\mathbb R$ be $\alpha$-strongly convex with respect to $\|\cdot\|_*$, with $\alpha>0$ and $\inf_{B\in\mathcal S}F(B)=0$. Let $\mathcal B\subseteq\{B\in\mathcal S:F(B)\le\beta^2\}$.
--
--   Fix features $x_1,\dots,x_n\in\mathbb R^p$, $n\ge1$, such that $\|\sigma x_i^\top\|\le\Omega$ for every $i$ and every $\sigma\in\{\pm1\}^d$. Let $\sigma_1,\dots,\sigma_n\in\{\pm1\}^d$ have i.i.d. Rademacher entries and put $\Theta=\frac1n\sum_{i=1}^n\sigma_ix_i^\top$. Then for every $\lambda>0$,
--   $$\mathbb E\Bigl[\sup_{B\in\mathcal B}\langle B,\Theta\rangle\Bigr]\le\frac{\beta^2}{\lambda}+\frac{\lambda\Omega^2}{2\alpha n}.$$
--
--   This is the per-sample bound in the proof of Theorem 6. When $\beta>0$ and $\Omega>0$, choosing $\lambda=(\beta/\Omega)\sqrt{2\alpha n}$ gives $\Omega\beta\sqrt{2/(\alpha n)}$. The zero cases follow by taking a limit in the bound for arbitrary $\lambda>0$; for a negative $\beta$, optimization gives the bound with $|\beta|$.
--
--   **Formalization Note** The expectation over the signs is the average over all $2^{nd}$ sign matrices, signs encoded by `Bool`. The norm is a seminorm that vanishes only at $0$. The hypothesis $\inf_{B\in\mathcal S}F(B)=0$ is stated as "$0$ is the greatest lower bound of $F(\mathcal S)$", which also requires $\mathcal S$ nonempty, as the printed infimum does. $\lambda$ is written `lam`. When $\mathcal B$ is empty the supremum is $0$ by Lean's convention, and the bound still holds because its right-hand side is nonnegative.
--
--   Differences from the source:
--
--   - encoding: E over i.i.d. Rademacher signs; a norm on ℝ^{d×p}; inf_{B∈𝒮} F(B) = 0 → average over all 2^{nd} sign matrices; definite Seminorm; IsGLB (F '' 𝒮) 0; reason: the same objects; same instances
--   - generalization: β is the nonnegative size parameter of Theorem 6 → β may be any real number in the arbitrary-λ bound; reason: Only β² occurs in the hypotheses and conclusion of this bound, so the signed extension specializes to every nonnegative source radius.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 34, Appendix C.2 (proof of Theorem 6), the display after 'Plugging this above'

import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Supplement_LinearClass

namespace SPOBounds.Natarajan.Supplement

/-- **Proof of Theorem 6, bound for arbitrary `λ > 0`** (arXiv:1905.11488v3, Appendix C.2,
p. 34). Let `N` be a norm on `ℝ^{d×p}` and `N_*` its dual norm under the trace pairing
`⟨B, A⟩ = ∑ B_{ij} A_{ij}`. Let `𝒮` be closed and convex, `F` `α`-strongly convex on `𝒮` with
respect to `N_*` (`α > 0`) with `inf_{B ∈ 𝒮} F(B) = 0`, and `ℬ ⊆ {B ∈ 𝒮 : F(B) ≤ β²}`. Fix
features `x₁, …, xₙ` (`n > 0`) with `N(σ xᵢᵀ) ≤ Ω` for every `i` and every `σ ∈ {±1}^d`. Then for
every `λ > 0`, with `Θ = (1/n) ∑ᵢ σᵢ xᵢᵀ` for uniform signs `σ ∈ {±1}^{n×d}`,
`E_σ[sup_{B ∈ ℬ} ⟨B, Θ⟩] ≤ β²/λ + λ Ω² / (2 α n)`; the expectation is the average over all
`2^{nd}` sign matrices. -/
theorem linear_rademacher_lambda_bound {d p n : ℕ}
    (N : Seminorm ℝ (Matrix (Fin d) (Fin p) ℝ)) (hN : IsMatrixNorm N)
    (𝒮 : Set (Matrix (Fin d) (Fin p) ℝ)) (h𝒮c : IsClosed 𝒮) (h𝒮v : Convex ℝ 𝒮)
    (F : Matrix (Fin d) (Fin p) ℝ → ℝ) (α : ℝ) (hα : 0 < α)
    (hF : StronglyConvexWrt (dualNorm N) 𝒮 α F) (hinf : IsGLB (F '' 𝒮) 0)
    (ℬ : Set (Matrix (Fin d) (Fin p) ℝ)) (β : ℝ) (hℬ : ℬ ⊆ {B | B ∈ 𝒮 ∧ F B ≤ β ^ 2})
    (Ω : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin p))
    (hx : ∀ i, ∀ σ : Fin d → Bool, N (signOuter σ (x i)) ≤ Ω)
    (hn : 0 < n) (lam : ℝ) (hlam : 0 < lam) :
    (1 / 2 ^ (n * d) : ℝ) * ∑ σ : Fin n → Fin d → Bool,
        (⨆ B : ℬ, matInner (B : Matrix (Fin d) (Fin p) ℝ)
          ((1 / n : ℝ) • ∑ i, signOuter (σ i) (x i))) ≤
      β ^ 2 / lam + lam * Ω ^ 2 / (2 * α * n) := by sorry

end SPOBounds.Natarajan.Supplement
