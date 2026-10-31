-- Prove2me | Theorems.Thm_RBMSensitivity_eq_9_1_lemma_9_1
-- name    : RBMSensitivity.eq_9_1_lemma_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:37:45.115712+00:00
-- url     : https://prove2.me/theorems/59297bb6-44e9-46ef-b8ac-4c13299a7d3d
-- title:
--   (9.1) and Lemma 9.1 — limits of $\theta_t$, $\theta_t'$ and the local dominator
-- statement:
--   Suppose the data satisfies Assumptions 2.2, 2.4 and 2.5, and the coefficients satisfy Assumptions 2.12 and 3.4. Fix a continuously differentiable $f:G\to\mathbb R$ with bounded and continuous Jacobian $f':G\to\mathbb R^{1\times J}$, let $x\in G$ and $\xi=(x,0)\in\mathbb X$, and for each $t>0$ define $\theta_t(\alpha):=\frac 1t\int_0^t\mathbb E[f(Z^{\alpha,x}(s))]\,ds$. Then $\theta_t$ is differentiable on $U$ with
--   $$\theta_t'(\alpha)=\frac 1t\int_0^t\mathbb E\big[f'(Z^{\alpha,x}(s))\mathcal J^{\alpha,\xi}(s)\big]\,ds,\qquad\alpha\in U,$$
--   and
--   $$\lim_{t\to\infty}\theta_t(\alpha)=\mathbb E[f(Z^{\alpha,x}(\infty))]\quad\text{and}\quad\lim_{t\to\infty}\theta_t'(\alpha)=\mathbb E\big[f'(Z^{\alpha,x}(\infty))\mathcal J^{\alpha,\xi}(\infty)\big].$$
--   **Lemma 9.1.** There exists a locally integrable function $\bar\theta:U\to[0,\infty)$ such that $|\theta_t'(\alpha)|\le\bar\theta(\alpha)$ for all $t>0$ and $\alpha\in U$.
--
--   These facts are exactly what the Fundamental Theorem of Calculus and dominated convergence need to pass to the goal theorem. They carry the interchange of the derivative in $\alpha$ with the limit $t\to\infty$.
--
--   Differences from the source:
--   - encoding: J-dimensional {F_t}-Brownian motion, defined by quadratic variation → IsFBrownian: adapted, a.s. continuous, started at 0, increments independent of F_s with law N(0,(t-s)E_J); reason: Lévy's characterization; quadratic variation is absent from Mathlib at this revision; same object
--   - encoding: the pathwise unique processes Z^{α,x}, J^{α,ξ} → any family Z, J satisfying Definitions 2.1, 2.10 with the given starts; reason: pathwise uniqueness makes the choice immaterial; Theorems 2.8 and 2.13 give existence
--   - encoding: probability measure on (X, B(X)) → probability measure on E J × E J with ν Xᶜ = 0, tested on Borel subsets of the product; reason: X is Borel in the product and the joint process stays in X a.s.; same objects
--   - encoding: f : G → ℝ continuously differentiable with bounded continuous Jacobian f' on G → f : E J → ℝ, ContDiffOn ℝ 1 f G, bound on fderivWithin ℝ f G; reason: G is closed and convex with nonempty interior, so it has unique derivatives and fderivWithin is f'; values of f off G are never used
--   - encoding: for all t ≥ 0, in the derivative formula and in Lemma 9.1 → t > 0; reason: θ_t is defined only for t > 0 (p.35), and 1/t is undefined at t = 0
--   - encoding: E[f(Z^{α,x}(∞))] and E[f'(Z^{α,x}(∞)) J^{α,ξ}(∞)] → ∫ f p.1 dμ(α) and ∫ f'(p.1) p.2 dμ(α), for μ(α) stationary; reason: by Remark 3.7 the law of Ξ^α(∞) is the unique stationary distribution
--   - generalization: the integrals are written without comment → the conclusion also asserts integrability in ω and under μ(α), and interval integrability in s; reason: true by Corollary 7.4; it rules out junk values of Bochner integrals, and dropping those clauses gives the source's claim
--   - encoding: continuous Z, Y (Definition 2.1) and RCLL J, K (Definition 2.10) processes → paths continuous, resp. RCLL, for almost every ω; reason: under the usual conditions a process with a.s. continuous (RCLL) paths is indistinguishable from an adapted process all of whose paths are continuous (RCLL): modify it on a P-null set, which lies in F_0; same processes up to indistinguishability
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §9, (9.1), Lemma 9.1, pp.35–36

import Mathlib
import Definitions.Def_RBMSensitivity_IsUsualFiltration
import Definitions.Def_RBMSensitivity_Data_Assumption_2_2
import Definitions.Def_RBMSensitivity_Data_Assumption_2_4
import Definitions.Def_RBMSensitivity_Data_Assumption_2_5
import Definitions.Def_RBMSensitivity_Data_Assumption_2_12
import Definitions.Def_RBMSensitivity_Data_Assumption_3_4
import Definitions.Def_RBMSensitivity_Data_IsJointFamily
import Definitions.Def_RBMSensitivity_Data_IsStationaryJoint
import Definitions.Def_RBMSensitivity_theta
import Definitions.Def_RBMSensitivity_Data_thetaDot
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- **(9.1) and Lemma 9.1**: arXiv:1907.00472v2, §9, pp.35–36. Fix a C¹ function `f : G → ℝ` with bounded
continuous Jacobian, `x ∈ G` and `ξ = (x, 0)`. For each `t > 0`, `θ_t` is differentiable on `U` with
`θ'_t(α) = (1/t) ∫_0^t E[f'(Z^{α,x}(s)) 𝒥^{α,ξ}(s)] ds`, and
`lim_{t→∞} θ_t(α) = E[f(Z^{α,x}(∞))]`, `lim_{t→∞} θ'_t(α) = E[f'(Z^{α,x}(∞)) 𝒥^{α,ξ}(∞)]` (9.1).
**Lemma 9.1:** there is a locally integrable `θ̄ : U → [0, ∞)` with `|θ'_t(α)| ≤ θ̄(α)` for all `t`, `α`.

**Formalization Note.** The law of `Ξ(∞)` is `μ α`. `t > 0` throughout, since `θ_0` is undefined. The
integrability clauses guard against junk values of Bochner integrals. One item: this is one display and its
lemma, the interchange of `d/dα` and `t → ∞` announced in the paper. -/
theorem eq_9_1_lemma_9_1 {J : ℕ} (hJ : 0 < J) (D : Data J) {B : ℝ → Set (E J)}
    (h22 : D.Assumption_2_2) (h24 : D.Assumption_2_4 B) (h25 : D.Assumption_2_5)
    (h212 : D.Assumption_2_12) (h34 : D.Assumption_3_4)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (h𝓕 : IsUsualFiltration 𝓕 P)
    {W : ℝ≥0 → Ω → E J} (hW : IsFBrownian 𝓕 P W)
    {Z : ℝ → E J → ℝ≥0 → Ω → E J} {𝒥 : ℝ → E J × E J → ℝ≥0 → Ω → E J}
    (hZ : D.IsJointFamily 𝓕 P W Z 𝒥)
    {μ : ℝ → Measure (E J × E J)} (hμ : ∀ α ∈ D.U, D.IsStationaryJoint P Z 𝒥 α (μ α))
    {f : E J → ℝ} (hf : ContDiffOn ℝ 1 f D.G)
    (hf' : ∃ C, ∀ x ∈ D.G, ‖fderivWithin ℝ f D.G x‖ ≤ C) {x : E J} (hx : x ∈ D.G) :
    (∀ α ∈ D.U, ∀ s : ℝ≥0, Integrable (fun ω => f (Z α x s ω)) P ∧
      Integrable (fun ω => fderivWithin ℝ f D.G (Z α x s ω) (𝒥 α (x, 0) s ω)) P) ∧
    (∀ t : ℝ, 0 < t → ∀ α ∈ D.U,
      IntervalIntegrable (fun s : ℝ => ∫ ω, f (Z α x s.toNNReal ω) ∂P) volume 0 t ∧
      IntervalIntegrable (fun s : ℝ =>
        ∫ ω, fderivWithin ℝ f D.G (Z α x s.toNNReal ω) (𝒥 α (x, 0) s.toNNReal ω) ∂P) volume 0 t ∧
      HasDerivAt (theta P Z f x t) (D.thetaDot P Z 𝒥 f x t α) α) ∧
    (∀ α ∈ D.U, Integrable (fun p => f p.1) (μ α) ∧
      Integrable (fun p => fderivWithin ℝ f D.G p.1 p.2) (μ α) ∧
      Tendsto (fun t => theta P Z f x t α) atTop (𝓝 (∫ p, f p.1 ∂μ α)) ∧
      Tendsto (fun t => D.thetaDot P Z 𝒥 f x t α) atTop
        (𝓝 (∫ p, fderivWithin ℝ f D.G p.1 p.2 ∂μ α))) ∧
    ∃ θbar : ℝ → ℝ, (∀ α ∈ D.U, 0 ≤ θbar α) ∧ LocallyIntegrableOn θbar D.U ∧
      ∀ t : ℝ, 0 < t → ∀ α ∈ D.U, |D.thetaDot P Z 𝒥 f x t α| ≤ θbar α := by sorry

end RBMSensitivity
