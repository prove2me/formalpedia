-- Prove2me | Theorems.Thm_PoissonDirichlet_Chain_theorem_38
-- name    : PoissonDirichlet.Chain.theorem_38
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:59:28.262973+00:00
-- url     : https://prove2.me/theorems/47f629c8-3322-44b7-ac6c-752f564e8829
-- title:
--   Theorem 38, pp. 887–888 (0 < α < 1) — PD(α, θ) is the K_{α,θ}Y_1^θ-tilt of P*_{α,θ}, (Y_n) is Markov under both, and the law of Σ_1
-- statement:
--   Let $0 < \alpha < 1$ and $\theta > -\alpha$. Let $P_{\alpha,\theta}$ govern $(V_n)$ with the $\mathrm{PD}(\alpha,\theta)$ distribution, with $R_n = V_{n+1}/V_n$ (21) and $Y_n = V_n/(V_n+V_{n+1}+\cdots)$ (45). Let $P^*_{\alpha,\theta}$ govern $(R_1, R_2, \dots)$ as a sequence of independent random variables with $R_n \sim \mathrm{beta}(\theta+n\alpha, 1)$, and $Y_n = (1+R_n+R_nR_{n+1}+\cdots)^{-1}$ (125). Let $r(\alpha,\theta',y)$ be defined by the first equality of (140):
--   $$r(\alpha,\theta',y)\,dy = \Gamma(\theta'/\alpha+1)\,y^{\theta'}\,P^*_{\alpha,\theta'}(V_1 \in dy), \qquad V_1 = Y_1,$$
--   for the parameters $\theta' = \theta + k\alpha$, $k = 0, 1, 2, \dots$. Then:
--
--   1. **(i)** For every nonnegative product measurable function $f$,
--   $$E_{\alpha,\theta}[f(Y_1, Y_2, \dots)] = K_{\alpha,\theta}\,E^*_{\alpha,\theta}[Y_1^\theta f(Y_1, Y_2, \dots)], \qquad K_{\alpha,\theta} = \Gamma(\theta+1)\Gamma(1-\alpha)^{\theta/\alpha}. \quad (137)\text{–}(138)$$
--   2. **(ii)** Both $P = P_{\alpha,\theta}$ and $P = P^*_{\alpha,\theta}$ govern $(Y_n)$ as a Markov chain with the same forward transition probabilities, given by
--   $$\frac{P(Y_{n+1} \in dy_{n+1} \mid Y_n = y_n)}{dy_{n+1}} = \alpha\,y_n^{-\alpha-1}(1-y_n)^{n\alpha+\theta-1}\,\frac{r(\alpha,\theta+n\alpha,y_{n+1})}{r(\alpha,\theta+n\alpha-\alpha,y_n)} \quad (139)$$
--   for $0<y_n<1$, $0<y_{n+1}<y_n/(1-y_n)$ and $0$ otherwise; moreover $r(\alpha,\theta,y)\,dy = C_{\alpha,\theta}^{-1}P_{\alpha,\theta}(V_1 \in dy)$ (140) with $C_{\alpha,\theta}$ as in (43).
--   3. **(iii)** The $P^*_{\alpha,\theta}$ distribution of $\Sigma_1 := (1-V_1)/V_1$ is infinitely divisible, with Laplace transform
--   $$E^*_{\alpha,\theta}[\exp(-\lambda\Sigma_1)] = \Big(\frac{1}{\psi_\alpha(\lambda)}\Big)^{\theta/\alpha+1} \quad (\lambda \ge 0). \quad (141)$$
--
--   The theorem extends the Markov chain description of $\mathrm{PD}(0,\theta)$ due to Vershik–Shmidt and Ignatov, and Proposition 8 for $\mathrm{PD}(\alpha,0)$, to the whole two-parameter family: the size-ordered frequencies of $\mathrm{PD}(\alpha,\theta)$ are, up to a density that depends on $Y_1$ only, built from independent beta ratios.
--
--   **Formalization Note.** The paper states Theorem 38 for $0 \le \alpha < 1$ and proves it for $0<\alpha<1$, quoting the case $\alpha = 0$ from [67], [34] (Remark 40); this item is the case $0<\alpha<1$. **(139) as printed lacks the factor $\alpha$**; the statement includes it (see the Setting definition `transDens`), since Bayes' rule from (128), (146) and the beta density produces it and Corollary 41's $\alpha^{n-1}$ agrees. The function $r$ is a hypothesis: any `rf` satisfying the first equality of (140) as an identity of measures on $\mathbb{R}$, $\int_s r(\alpha,\theta',y)\,dy = E^*_{\alpha,\theta'}[\Gamma(\theta'/\alpha+1)Y_1^{\theta'}; Y_1 \in s]$ for every Borel $s$ and every $\theta' = \theta+k\alpha$ (so $r$ vanishes almost everywhere off $(0,1)$, and $y^{\theta'}$ is only evaluated at $Y_1 \in (0,1)$); such functions exist and differ only on null sets. Markov chains are stated through `IsMarkovWith`, a common family of Markov kernels for both laws, and the explicit density (139) is stated in the same defining form under each law. Laplace transforms and all expectations of nonnegative quantities are lower Lebesgue integrals. Infinite divisibility: for every $m \ge 1$ some probability measure has $m$-fold convolution power equal to the law of $\Sigma_1$. 0-based indices: `Yseq (V ω) k` and `YofR r k` are $Y_{k+1}$.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), pp. 887–888, Theorem 38, (137)–(141); Remark 40, p. 888

import Mathlib
import Definitions.Def_PoissonDirichlet_Chain_Setting
import Definitions.Def_PoissonDirichlet_Chain_Markov
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Chain

/-- Theorem 38, pp. 887–888, for `0 < α < 1`, `θ > -α`, 0-based (`Y ω k` is `Y_{k+1}`).
`P` governs `(V_n)` with `PD(α, θ)` law and `Y = Yseq V` (45); `μ` is `P*_{α,θ}`, under which the
ratios `R_n` are independent `beta(θ + nα, 1)` and `Y = YofR R` (125). `rf θ' y` is
`r(α, θ', y)` of (140), first equality, for the parameters `θ' = θ + kα` used in (139), stated
as the identity of measures `r(α, θ', y) dy = Γ(θ'/α + 1) y^{θ'} P*_{α,θ'}(Y_1 ∈ dy)` on `ℝ`.
1. (137)–(138): `E_{α,θ}[f(Y_1, Y_2, …)] = K_{α,θ} E*_{α,θ}[Y_1^θ f(Y_1, Y_2, …)]` with
   `K_{α,θ} = Γ(θ + 1) Γ(1 - α)^{θ/α}`.
2. (ii): both `P` and `P*_{α,θ}` govern `(Y_n)` as a Markov chain with the same forward
   transition probabilities; these have density (139) (with the factor `α` the printed (139)
   omits, see `transDens`); and (140), second equality, `r(α, θ, y) dy = C_{α,θ}^{-1}
   P_{α,θ}(V_1 ∈ dy)`.
3. (iii), (141): the `P*_{α,θ}` law of `Σ_1 = (1 - V_1)/V_1` has Laplace transform
   `(1/ψ_α(λ))^{θ/α+1}` and is infinitely divisible.
The case `α = 0` of the theorem is quoted by the paper from [67], [34] and is not part of this
statement (Remark 40). -/
theorem theorem_38 (α θ : ℝ) (hα : 0 < α) (hα1 : α < 1) (hθ : -α < θ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α θ P V) (μ : Measure (ℕ → ℝ)) (hμ : IsStarLaw α θ μ)
    (rf : ℝ → ℝ → ℝ)
    (hr140 : ∀ k : ℕ, ∀ μ' : Measure (ℕ → ℝ), IsStarLaw α (θ + (k : ℝ) * α) μ' →
      ∀ s : Set ℝ, MeasurableSet s →
        ∫⁻ y in s, ENNReal.ofReal (rf (θ + (k : ℝ) * α) y) =
          ∫⁻ r, s.indicator (fun y => ENNReal.ofReal
            (Real.Gamma ((θ + (k : ℝ) * α) / α + 1) * y ^ (θ + (k : ℝ) * α))) (YofR r 0) ∂μ') :
    -- (i), (137)–(138)
    (∀ f : (ℕ → ℝ) → ENNReal, Measurable f →
      ∫⁻ ω, f (Yseq (V ω)) ∂P =
        ENNReal.ofReal (chainConst α θ) * ∫⁻ r, ENNReal.ofReal (YofR r 0 ^ θ) * f (YofR r) ∂μ) ∧
    -- (ii): one family of forward transition kernels for both laws
    (∃ κ : ℕ → Kernel ℝ ℝ, (∀ k, IsMarkovKernel (κ k)) ∧
      IsMarkovWith P (fun ω => Yseq (V ω)) κ ∧ IsMarkovWith μ (fun r => YofR r) κ) ∧
    -- (ii), (139): the forward transition density, under `P_{α,θ}` and under `P*_{α,θ}`
    (∀ k : ℕ, ∀ g : (Fin (k + 1) → ℝ) → ENNReal, Measurable g →
      ∀ h : ℝ → ENNReal, Measurable h →
        ∫⁻ ω, g (fun i => Yseq (V ω) i) * h (Yseq (V ω) (k + 1)) ∂P =
          ∫⁻ ω, g (fun i => Yseq (V ω) i) *
            (∫⁻ z, ENNReal.ofReal (transDens α θ rf k (Yseq (V ω) k) z) * h z) ∂P) ∧
    (∀ k : ℕ, ∀ g : (Fin (k + 1) → ℝ) → ENNReal, Measurable g →
      ∀ h : ℝ → ENNReal, Measurable h →
        ∫⁻ r, g (fun i => YofR r i) * h (YofR r (k + 1)) ∂μ =
          ∫⁻ r, g (fun i => YofR r i) *
            (∫⁻ z, ENNReal.ofReal (transDens α θ rf k (YofR r k) z) * h z) ∂μ) ∧
    -- (140), second equality
    (∀ s : Set ℝ, MeasurableSet s →
      ∫⁻ y in s, ENNReal.ofReal (rf θ y) =
        ENNReal.ofReal (1 / PoissonDirichlet.Moments.pdConst α θ) * P ((fun ω => V ω 0) ⁻¹' s)) ∧
    -- (iii), (141), and infinite divisibility
    (∀ l : ℝ, 0 ≤ l →
      ∫⁻ r, ENNReal.ofReal (Real.exp (-l * SigofR r)) ∂μ =
        ENNReal.ofReal ((1 / PoissonDirichlet.Wendel.psi α l) ^ (θ / α + 1))) ∧
    (∀ m : ℕ, 1 ≤ m → ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      ∀ s : Set ℝ, MeasurableSet s → convPow ν m s = μ (SigofR ⁻¹' s)) := by sorry

end PoissonDirichlet.Chain
