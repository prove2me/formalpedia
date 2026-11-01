-- Prove2me | Theorems.Thm_VRAccelCLT_theorem_2
-- name    : VRAccelCLT.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:51.617306+00:00
-- url     : https://prove2.me/theorems/0d8b0f0e-f312-4e5c-ac8d-51a30ee6b957
-- title:
--   Theorem 2: CLT for Algorithm 2 with geometrically increasing $N_k$
-- statement:
--   Let $f:\mathbb R^m\to\mathbb R$ satisfy Assumption 1 with constants $L,\eta>0$ and minimizer $x^*$, and Assumption 2: the Hessian condition (29) at $x^*$ with matrix $H$ and constant $R_D>0$, and the noise conditions (30)–(31) with limit covariance $S_0$, on top of (5) with constant $\nu>0$. Consider Algorithm 2 from $x_0=y_0$ with
--
--   $$
--   \alpha\in(0,1/L],\qquad \gamma=\sqrt{\alpha\eta},\qquad \beta=\frac{1-\gamma}{1+\gamma},\qquad N_k=\big\lceil\rho_2^{-(k+1)}\big\rceil,\quad \rho_2\in(1-\gamma,1).
--   $$
--
--   Let
--
--   $$
--   P_2=\rho_2^{-1/2}\begin{pmatrix}(1+\beta)(I_m-\alpha H) & -\beta(I_m-\alpha H)\\ I_m & 0_m\end{pmatrix}.
--   $$
--
--   Then $\rho(P_2)<1$, the series $\Sigma_2=\sum_{t=0}^{\infty}P_2^t\begin{pmatrix}S_0&0_m\\0_m&0_m\end{pmatrix}(P_2^t)^T$ converges, and
--
--   $$
--   \alpha^{-1}\rho_2^{-k/2}\begin{pmatrix}y_k-x^*\\ y_{k-1}-x^*\end{pmatrix}\ \xrightarrow[k\to\infty]{d}\ N(0,\Sigma_2).
--   $$
--
--   The accelerated stochastic gradient method with geometrically growing batches is therefore asymptotically normal at the rate $\rho_2^{k/2}$, with an explicit covariance. This is the basis for confidence statements about $x^*$ built from the iterates of the accelerated method.
--
--   **Formalization Note** $\mathbb R^{2m}$ carries the stacked vector with $y_k-x^*$ as first block. At $k=0$ the term $y_{k-1}$ reads $y_0$; one index does not affect the limit. $\rho$ is the complex spectral radius. $N(0,\Sigma_2)$ is Mathlib's multivariate Gaussian.
--
--   Differences from the source:
--   - generalization: noise w_{k,N_k} = sampled average (3) under Assumption 1(iii) → any F_{k+1}-measurable square-integrable noise w_k with (5) for a filtration F; reason: the paper derives (5) from (3) and Assumption 1(iii) (p.6) and uses nothing else about the noise; the sampled noise is an instance
--   - generalization: Algorithm 2 with positive β → β = (1−γ)/(1+γ) ≥ 0, allowed to be 0; reason: the theorem's own choice gives β = 0 when αη = 1 (η = L, α = 1/L); for β > 0 it is the source's statement
--   - encoding: x* the unique optimal solution, f* = f(x*) → x* any minimizer of f (∀ z, f x* ≤ f z), f* = f(x*); reason: strong convexity makes the minimizer unique; same instances
--   - encoding: (29): ∇f(x) = H(x−x*) + D(x)(x−x*), ‖D(x)‖ ≤ R_D‖x−x*‖ → ‖∇f(x) − H(x−x*)‖ ≤ R_D‖x−x*‖²; reason: equivalent: take D(x) = (∇f(x) − H(x−x*))(x−x*)ᵀ/‖x−x*‖²; the bound also makes H the derivative of ∇f at x*
--   - encoding: (30) matrix limits a.s.; (31) lim_{r→∞} sup_k E[…] = 0 → (30) entrywise; (31) as ∀ε>0 ∃R ∀r≥R ∀k, E[…] ≤ ε with a lower Lebesgue integral; reason: equivalent; avoids a real supremum
--   - encoding: (y_k − x*; y_{k−1} − x*) for k ≥ 1 → y_{k−1} read with natural-number subtraction (y_0 at k = 0); reason: a single index does not affect convergence in distribution
--   - encoding: Σ2 ≜ Σ_t P2^t (S0 0; 0 0) (P2^t)ᵀ → the conclusion also asserts summability of the series; reason: a non-summable tsum is 0 in Lean; the paper's definition presupposes convergence
-- source:
--   Lei, Shanbhag, Variance-Reduced Accelerated First-order Methods: Central Limit Theorems and Confidence Statements, arXiv:2006.07769v3, Theorem 2, p.19; proof pp.19–20

import Mathlib
import Definitions.Def_VRAccelCLT_specRad
import Definitions.Def_VRAccelCLT_batchSize
import Definitions.Def_VRAccelCLT_SmoothStronglyConvex
import Definitions.Def_VRAccelCLT_IsVRNoise
import Definitions.Def_VRAccelCLT_Assumption2i
import Definitions.Def_VRAccelCLT_Assumption2ii
import Definitions.Def_VRAccelCLT_IsAlg2Run
import Definitions.Def_VRAccelCLT_P2
import Definitions.Def_VRAccelCLT_Sigma2
import Definitions.Def_VRAccelCLT_stack

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace VRAccelCLT

/-- **Theorem 2 (CLT for Algorithm 2 with geometrically increasing `N_k`).** Lei, Shanbhag,
arXiv:2006.07769v3, Theorem 2, p.19: "Suppose Assumptions 1 and 2 hold. Consider Algorithm 2, where
α ∈ (0, 1/L], γ ≜ √αη, β ≜ (1−γ)/(1+γ), and Nk ≜ ⌈ρ2^{−(k+1)}⌉ with ρ2 ∈ (1 − γ, 1). Then
α^{−1}ρ2^{−k/2} (yk − x∗ ; yk−1 − x∗) →d N(0, Σ2) with Σ2 ≜ Σ_{t=0}^∞ P2^t (S0 0m ; 0m 0m) (P2^t)^T,
where P2 ≜ ρ2^{−1/2} ((1 + β)(Im − αH) −β(Im − αH) ; Im 0m) and ρ(P2) < 1."

Conclusion: `ρ(P₂) < 1`, the series defining `Σ₂` is summable, and the scaled stacked error
converges in distribution to `N(0, Σ₂)`.

**Formalization Note.** `ℝᵐ` is `EuclideanSpace ℝ (Fin m)`, `ℝ^{2m}` is
`EuclideanSpace ℝ (Fin m ⊕ Fin m)` (`stack`, blocks via `Matrix.fromBlocks`). The noise is any
`w` with (5) (`IsVRNoise`), of which the sampled noise (3) under Assumption 1 (iii) is an instance.
At `k = 0` the term `y_{k−1}` reads `y_0` (natural-number subtraction); a single index does not
affect the limit. `ρ(·)` is `specRad` (complex spectrum). `β` may be `0` (when `αη = 1`). The
summability clause guards the `tsum` in `Σ₂`. -/
theorem theorem_2 {m : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (L η ν RD α γ β ρ₂ : ℝ) (x0 xstar : EuclideanSpace ℝ (Fin m))
    (H S0 : Matrix (Fin m) (Fin m) ℝ) (w x y : ℕ → Ω → EuclideanSpace ℝ (Fin m))
    (hA1 : SmoothStronglyConvex f L η) (hmin : ∀ z, f xstar ≤ f z)
    (hA2i : Assumption2i f xstar H RD)
    (hw : IsVRNoise μ ℱ w ν (batchSize ρ₂)) (hA2ii : Assumption2ii μ ℱ w (batchSize ρ₂) S0)
    (hα : 0 < α) (hαL : α ≤ 1 / L) (hγ : γ = Real.sqrt (α * η)) (hβ : β = (1 - γ) / (1 + γ))
    (hρ : 1 - γ < ρ₂) (hρ1 : ρ₂ < 1)
    (hrun : IsAlg2Run f α β x0 w x y) :
    specRad (P2 ρ₂ α β H) < 1 ∧
    Summable (fun t : ℕ =>
      P2 ρ₂ α β H ^ t * Matrix.fromBlocks S0 0 0 0 * (P2 ρ₂ α β H ^ t).transpose) ∧
    TendstoInDistribution
      (fun (k : ℕ) (ω : Ω) =>
        (α⁻¹ * ρ₂ ^ (-(k : ℝ) / 2)) • stack (y k ω - xstar) (y (k - 1) ω - xstar))
      atTop id (fun _ => μ) (multivariateGaussian 0 (Sigma2 ρ₂ α β H S0)) := by sorry

end VRAccelCLT
