-- Prove2me | Theorems.Thm_SOSInference_Means_eq_22
-- name    : SOSInference.Means.eq_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:55.104255+00:00
-- url     : https://prove2.me/theorems/39455383-91ff-4280-81e2-35cdf1b0fe18
-- title:
--   (21)–(22) — LP duality for the SOS function
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^l$ ($n\ge1$), and let $(z_j)_{j\in J}$ be a finite family of points of $\mathbb R^l$ that contains every $x_i$ (as the merged sample $\mathcal Z_{n+m}$ contains $\mathcal X_n$). Take the target mean $\theta_*=0$ and assume that the linear program (21) is feasible, i.e. that $0$ lies in the convex hull of the $z_j$. Then the SOS value equals the optimal value of the simplified dual problem, and the dual maximum is attained:
--   $$R_n^W(0)=\max_{\lambda\in\mathbb R^l,\ \gamma_i\ge0}\Big\{-\lambda^{\mathsf T}\bar X_n-\frac1n\sum_{i=1}^n\gamma_i\Big\}\quad\text{s.t.}\quad -\lambda^{\mathsf T}x_i-\gamma_i\le\inf_j\big\{-\lambda^{\mathsf T}z_j+\|x_i-z_j\|_2^2\big\}\ \ \text{for all } i .$$
--
--   This is the starting point of the asymptotic analysis: it replaces a minimisation over couplings by a maximisation over a single vector $\lambda$ and $n$ slacks, each controlled by the distance from $x_i$ to the support points.
--
--   **Formalization Note** The paper reduces to $\theta_*=0$ "without loss of generality" and uses strong duality for the event, of probability tending to one, that the LP is feasible; feasibility is a hypothesis here. The hypothesis that every $x_i$ is some $z_j$ is the paper's $Z_k=X_k$, $k\le n$.
-- source:
--   Blanchet, Kang, Sample Out-of-Sample Inference Based on Wasserstein Distance, arXiv:1605.01340v4, pp. 35–36, (21), (22)

import Mathlib
import Definitions.Def_SOSInference_Means_sos

namespace SOSInference.Means

open scoped RealInnerProductSpace

/-- **(21)–(22)**, §7.1, pp. 35–36 (Blanchet, Kang, Sample Out-of-Sample Inference Based on
Wasserstein Distance, arXiv:1605.01340v4, pp. 35–36, (21), (22)): LP duality for the SOS function.

Let `x_1, …, x_n` (`n ≥ 1`) be points of `ℝ^l` and `z` a finite family containing every `x_i`
(as `Z_{n+m} ⊇ X_n`). Take `θ* = 0` (p. 35: "without loss of generality we assume `θ* = 0`")
and assume the LP (21) is feasible. Then the optimal value `R_n^W(0)` of (21) equals the maximum
of the simplified dual (22):
`max_{λ, γ_i ≥ 0} {−λᵀX̄_n − (1/n) Σ_i γ_i}` subject to
`−λᵀx_i − γ_i ≤ inf_j {−λᵀz_j + ‖x_i − z_j‖₂²}` for all `i`,
and the maximum is attained.

**Formalization Note.** "max" is `IsGreatest` of the set of dual objective values. The paper
invokes strong duality where the LP is feasible ("for all `n` large enough with probability
one", p. 35); feasibility is the hypothesis `hfeas`. The hypothesis `hx` is the paper's
`Z_k = X_k`, `k ≤ n`, which turns the `j = i` constraint into `γ_i ≥ 0`. -/
theorem eq_22 {l n : ℕ} {ι : Type*} [Fintype ι] (hn : 0 < n) (x : Fin n → E l) (z : ι → E l)
    (hx : ∀ i, ∃ j, z j = x i) (hfeas : ∃ cpl, IsFeasibleCoupling (n := n) z 0 cpl) :
    IsGreatest
      {v : ℝ | ∃ (lam : E l) (γ : Fin n → ℝ), (∀ i, 0 ≤ γ i) ∧
        (∀ i, -⟪lam, x i⟫ - γ i ≤ ⨅ j, (-⟪lam, z j⟫ + ‖x i - z j‖ ^ 2)) ∧
        v = -⟪lam, xbar x⟫ - (1 / (n : ℝ)) * ∑ i, γ i}
      (sos x z 0) := by sorry

end SOSInference.Means
