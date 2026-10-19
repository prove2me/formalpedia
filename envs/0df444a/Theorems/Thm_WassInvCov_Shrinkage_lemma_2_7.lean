-- Prove2me | Theorems.Thm_WassInvCov_Shrinkage_lemma_2_7
-- name    : WassInvCov.Shrinkage.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:29:37.689905+00:00
-- url     : https://prove2.me/theorems/54c73fa2-4a9a-4525-946b-1a42e433fb2a
-- title:
--   Lemma 2.7, p. 7 — continuity properties of partial infima
-- statement:
--   Let $\mathcal E$ be a normed space, $\Gamma$ an index set, $\varphi:\mathcal E\times\Gamma\to\mathbb R$, and define the partial infimum
--
--   $$\Phi(\varepsilon)=\inf_{\gamma\in\Gamma}\varphi(\varepsilon,\gamma)\in[-\infty,+\infty],\qquad \varepsilon\in\mathcal E.$$
--
--   Let $\varepsilon_0\in\mathcal E$.
--   1. If $\varepsilon\mapsto\varphi(\varepsilon,\gamma)$ is continuous at $\varepsilon_0$ for every $\gamma\in\Gamma$, then $\Phi$ is upper semicontinuous at $\varepsilon_0$.
--   2. If $\varphi$ is calm from below at $\varepsilon_0$ uniformly in $\gamma$, that is, there is a constant $L\ge0$ with $\varphi(\varepsilon,\gamma)-\varphi(\varepsilon_0,\gamma)\ge-L\|\varepsilon_0-\varepsilon\|$ for all $\varepsilon\in\mathcal E$ and $\gamma\in\Gamma$, then $\Phi$ is lower semicontinuous at $\varepsilon_0$.
--
--   The paper uses this lemma to pass from positive definite to singular sample covariance matrices in the proof of Proposition 2.8.
--
--   **Formalization Note** The page asks $\mathcal E$ and $\Gamma$ to be normed spaces; here $\mathcal E$ is a normed additive group and $\Gamma$ an arbitrary type (the norm of $\Gamma$ is never used, and the paper's own application takes $\Gamma=\{\gamma:\gamma I\succ X\}$, which is not a normed space). $\Phi$ is computed in the extended reals, since the infimum may be $-\infty$ (or $+\infty$ for empty $\Gamma$). The calmness inequality is required for all $\varepsilon$, the literal reading of the page.
-- source:
--   Nguyen, Kuhn & Mohajerin Esfahani, Distributionally Robust Inverse Covariance Estimation, arXiv:1805.07194v1, p. 7, Lemma 2.7

import Mathlib

namespace WassInvCov.Shrinkage

/-- Lemma 2.7, p. 7 (arXiv:1805.07194v1): continuity properties of the partial infimum
`Φ(ε) = inf_{γ ∈ Γ} φ(ε, γ)`, computed in `EReal`.
(i) If `φ(·, γ)` is continuous at `ε₀` for every `γ`, then `Φ` is upper semicontinuous at `ε₀`.
(ii) If `φ` is calm from below at `ε₀` uniformly in `γ` — there is `L ≥ 0` with
`φ(ε, γ) − φ(ε₀, γ) ≥ −L‖ε₀ − ε‖` for all `ε` and `γ` — then `Φ` is lower semicontinuous at `ε₀`.
Here `ε` ranges over a normed group `E` and `Γ` is an arbitrary index type. -/
theorem lemma_2_7 {E Γ : Type*} [NormedAddCommGroup E] (ϕ : E → Γ → ℝ) (ε₀ : E) :
    ((∀ γ, ContinuousAt (fun ε => ϕ ε γ) ε₀) →
      UpperSemicontinuousAt (fun ε => ⨅ γ, (ϕ ε γ : EReal)) ε₀) ∧
    ((∃ L : ℝ, 0 ≤ L ∧ ∀ ε γ, ϕ ε γ - ϕ ε₀ γ ≥ -L * ‖ε₀ - ε‖) →
      LowerSemicontinuousAt (fun ε => ⨅ γ, (ϕ ε γ : EReal)) ε₀) := by sorry

end WassInvCov.Shrinkage
