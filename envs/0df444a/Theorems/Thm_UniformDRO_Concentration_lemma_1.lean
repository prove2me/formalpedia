-- Prove2me | Theorems.Thm_UniformDRO_Concentration_lemma_1
-- name    : UniformDRO.Concentration.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:02:48.941986+00:00
-- url     : https://prove2.me/theorems/4a3385a0-0652-44d4-86ab-b6aefacad9fc
-- title:
--   Lemma 1, p. 6 — duality R_k(Z; P) = inf_η { c_k(ρ) E_P[(Z − η)₊^{k*}]^{1/k*} + η }
-- statement:
--   Let $P$ be a probability measure on $(\mathcal X,\mathcal A)$, $k\in(1,\infty)$, $k_*=k/(k-1)$, $\rho>0$ and $c_k(\rho)=(1+k(k-1)\rho)^{1/k}$. Let $Z=\ell(\theta;\cdot)$ be a loss with $\mathbb E_P|Z|^{k_*}<\infty$. Then the Cressie–Read robust risk $\mathcal R_k(Z;P)=\sup\{\mathbb E_P[LZ]: L\ge0,\ \mathbb E_P[L]=1,\ \mathbb E_P[f_k(L)]\le\rho\}$ satisfies
--   $$
--   \mathcal R_k(Z;P)=\inf_{\eta\in\mathbb R}\Big\{c_k(\rho)\,\mathbb E_P\big[(Z-\eta)_+^{k_*}\big]^{1/k_*}+\eta\Big\}.
--   $$
--
--   The robust risk is thus a one-dimensional convex minimization: it penalizes the $L^{k_*}(P)$-norm of the loss above a threshold $\eta$. Every finite-sample result of Section 4 works with this dual form.
--
--   **Formalization Note** The page states the identity for all $\theta$ with $Z=\ell(\theta;\cdot)$; it is stated here for one loss $Z$. The hypothesis $Z\in L^{k_*}(P)$ is added: without it both sides are $+\infty$ (p. 6, "if the loss has finite $k_*$-moments"), while the Lean values are real. Under it the robust risk's value set is nonempty and bounded above (Hölder, as $\mathbb E_P[L^k]\le c_k(\rho)^k$), and $\eta\mapsto g_k(\eta;P)$ is bounded below by $\mathbb E_P[Z]$, so the real supremum and infimum are the paper's.
-- source:
--   Duchi & Namkoong, arXiv:1810.08750v6, Lemma 1, eq. (8), p. 6; proof App. A.1, p. 33

import Mathlib
import Definitions.Def_UniformDRO_Concentration_RobustRisk

open MeasureTheory

namespace UniformDRO.Concentration

/-- Lemma 1 (Duchi & Namkoong, arXiv:1810.08750v6, p. 6, eq. (8)): for a probability measure `P`,
`k ∈ (1, ∞)`, `ρ > 0` and a loss `Z = ℓ(θ; ·)` with finite `k*`-th moment,
`R_k(Z; P) = inf_{η ∈ ℝ} { c_k(ρ) E_P[(Z - η)_+^{k*}]^{1/k*} + η }`.
The `k*`-moment hypothesis is added: without it both sides are `+∞` (p. 6), and it makes the
robust risk's value set bounded above (Hölder) and the dual objective bounded below by `E_P[Z]`,
so the real `sSup` and `⨅` are the paper's supremum and infimum. -/
theorem lemma_1 {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (Z : X → ℝ)
    (hZ : MemLp Z (ENNReal.ofReal (kstar k)) P) :
    robustRisk k ρ P Z = ⨅ η : ℝ, dualObjective k ρ P Z η := by sorry

end UniformDRO.Concentration
