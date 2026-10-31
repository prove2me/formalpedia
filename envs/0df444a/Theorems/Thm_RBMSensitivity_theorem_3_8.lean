-- Prove2me | Theorems.Thm_RBMSensitivity_theorem_3_8
-- name    : RBMSensitivity.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:37:40.98324+00:00
-- url     : https://prove2.me/theorems/c00efac1-afc8-4399-8683-a6f307714422
-- title:
--   Theorem 3.8 — derivatives of stationary expectations of RBM via the joint process
-- statement:
--   Suppose the data $\{(d_i(\cdot),n_i),i\in\mathcal I\}$ satisfies Assumptions 2.2, 2.4 and 2.5, and the coefficients $b(\cdot)$, $\sigma(\cdot)$ and $R(\cdot)$ satisfy Assumptions 2.12 and 3.4. Let $f:G\to\mathbb R$ be continuously differentiable with bounded and continuous Jacobian $f':G\to\mathbb R^{1\times J}$, and define $F(\alpha):=\mathbb E[f(Z^\alpha(\infty))]$ for $\alpha\in U$. Then for almost every $\alpha\in U$ the function $F(\cdot)$ is differentiable and its Jacobian satisfies
--   $$F'(\alpha)=\mathbb E\big[f'(Z^\alpha(\infty))\mathcal J^\alpha(\infty)\big].$$
--   Here $\Xi^\alpha(\infty)=(Z^\alpha(\infty),\mathcal J^\alpha(\infty))$ has the unique stationary distribution of the joint process.
--
--   This expresses the sensitivity of a stationary expectation of the RBM to its drift, covariance and directions of reflection as a stationary expectation of the joint process. It affirms a conjecture of Dieker and Gao in a more general multidimensional setting.
--
--   Differences from the source:
--   - encoding: J-dimensional {F_t}-Brownian motion, defined by quadratic variation → IsFBrownian: adapted, a.s. continuous, started at 0, increments independent of F_s with law N(0,(t-s)E_J); reason: Lévy's characterization; quadratic variation is absent from Mathlib at this revision; same object
--   - encoding: the pathwise unique processes Z^{α,x}, J^{α,ξ} → any family Z, J satisfying Definitions 2.1, 2.10 with the given starts; reason: pathwise uniqueness makes the choice immaterial; Theorems 2.8 and 2.13 give existence
--   - encoding: probability measure on (X, B(X)) → probability measure on E J × E J with ν Xᶜ = 0, tested on Borel subsets of the product; reason: X is Borel in the product and the joint process stays in X a.s.; same objects
--   - encoding: f : G → ℝ continuously differentiable with bounded continuous Jacobian f' on G → f : E J → ℝ, ContDiffOn ℝ 1 f G, bound on fderivWithin ℝ f G; reason: G is closed and convex with nonempty interior, so it has unique derivatives and fderivWithin is f'; values of f off G are never used
--   - encoding: F(α) := E[f(Z^α(∞))], with Ξ^α(∞) of Remark 3.7 → F(α) := ∫ f p.1 dμ(α), for any family μ of stationary distributions; reason: the law of Ξ^α(∞) is the unique stationary distribution (Theorem 3.6)
--   - generalization: F is written without comment on integrability → the conclusion also asserts that f(x) and f'(x)y are integrable under μ(α), for every α ∈ U; reason: true by Corollary 7.4 and Fatou; it rules out junk values of Bochner integrals, and dropping those clauses gives the source's claim
--   - encoding: continuous Z, Y (Definition 2.1) and RCLL J, K (Definition 2.10) processes → paths continuous, resp. RCLL, for almost every ω; reason: under the usual conditions a process with a.s. continuous (RCLL) paths is indistinguishable from an adapted process all of whose paths are continuous (RCLL): modify it on a P-null set, which lies in F_0; same processes up to indistinguishability
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Theorem 3.8, (3.4), p.11

import Mathlib
import Definitions.Def_RBMSensitivity_IsUsualFiltration
import Definitions.Def_RBMSensitivity_Data_Assumption_2_2
import Definitions.Def_RBMSensitivity_Data_Assumption_2_4
import Definitions.Def_RBMSensitivity_Data_Assumption_2_5
import Definitions.Def_RBMSensitivity_Data_Assumption_2_12
import Definitions.Def_RBMSensitivity_Data_Assumption_3_4
import Definitions.Def_RBMSensitivity_Data_IsJointFamily
import Definitions.Def_RBMSensitivity_Data_IsStationaryJoint
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- **Theorem 3.8**: arXiv:1907.00472v2, (3.4), p.11. Suppose the data satisfies Assumptions 2.2, 2.4 and 2.5,
and the coefficients satisfy Assumptions 2.12 and 3.4. Let `f : G → ℝ` be continuously differentiable with
bounded and continuous Jacobian, and `F(α) := E[f(Z^α(∞))]`. Then for almost every `α ∈ U` the function `F` is
differentiable and `F'(α) = E[f'(Z^α(∞)) 𝒥^α(∞)]`.

**Formalization Note.** `μ α` is the law of `Ξ^α(∞) = (Z^α(∞), 𝒥^α(∞))` (Remark 3.7): the stationary
distribution, which exists and is unique by Theorem 3.6. So `F(α)` is `∫ p, f p.1 ∂μ α`. `f'(x)y` is
`fderivWithin ℝ f G x y`. The two integrability clauses make `F` and the right side genuine, so the identity
cannot hold through a junk value `0`. The derivative is the usual two-sided one, at a point of the open set
`U`. -/
theorem theorem_3_8 {J : ℕ} (hJ : 0 < J) (D : Data J) {B : ℝ → Set (E J)}
    (h22 : D.Assumption_2_2) (h24 : D.Assumption_2_4 B) (h25 : D.Assumption_2_5)
    (h212 : D.Assumption_2_12) (h34 : D.Assumption_3_4)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (h𝓕 : IsUsualFiltration 𝓕 P)
    {W : ℝ≥0 → Ω → E J} (hW : IsFBrownian 𝓕 P W)
    {Z : ℝ → E J → ℝ≥0 → Ω → E J} {𝒥 : ℝ → E J × E J → ℝ≥0 → Ω → E J}
    (hZ : D.IsJointFamily 𝓕 P W Z 𝒥)
    {μ : ℝ → Measure (E J × E J)} (hμ : ∀ α ∈ D.U, D.IsStationaryJoint P Z 𝒥 α (μ α))
    {f : E J → ℝ} (hf : ContDiffOn ℝ 1 f D.G)
    (hf' : ∃ C, ∀ x ∈ D.G, ‖fderivWithin ℝ f D.G x‖ ≤ C) :
    (∀ α ∈ D.U, Integrable (fun p => f p.1) (μ α)) ∧
    (∀ α ∈ D.U, Integrable (fun p => fderivWithin ℝ f D.G p.1 p.2) (μ α)) ∧
    ∀ᵐ α ∂(volume.restrict D.U),
      HasDerivAt (fun β => ∫ p, f p.1 ∂μ β) (∫ p, fderivWithin ℝ f D.G p.1 p.2 ∂μ α) α := by sorry

end RBMSensitivity
