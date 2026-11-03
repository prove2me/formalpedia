-- Prove2me | Theorems.Thm_RegimeDRCVaR_lemma_EC1
-- name    : RegimeDRCVaR.lemma_EC1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:24:25.911741+00:00
-- url     : https://prove2.me/theorems/26b78b50-cf92-4d92-a118-2afa8bf91f67
-- title:
--   Lemma EC.1 — the return marginals of $\mathcal U_{rs}(\boldsymbol\theta)$ are the regime mixtures of Wasserstein balls (corrected: regime budget of (9))
-- statement:
--   Let $K$ regimes have return samples $r_{nk}\in\mathbb R^I$ ($n\in[N_k]$, $N_k\ge1$), regime probabilities $w_k\ge0$ with $\sum_k w_k=1$, radii $\theta_k\ge0$, and let $m\in[1,+\infty]$. Write $\hat{\mathbb P}_k=\frac1{N_k}\sum_{n\in[N_k]}\delta_{r_{nk}}$ and $\Pi_{\tilde r}\,\mathcal U_{rs}(\boldsymbol\theta)$ for the set of laws of $\tilde r$ under the members of $\mathcal U_{rs}(\boldsymbol\theta)$. Then
--   $$
--   \Pi_{\tilde r}\,\mathcal U_{rs}(\boldsymbol\theta)=\Big\{\mathbb P \;:\; \mathbb P=\sum_{k\in[K]}w_k\mathbb P_k,\ \ W_m(\mathbb P_k,\hat{\mathbb P}_k)\le\theta_k\ \ \forall k\Big\}.
--   $$
--
--   The regime-switching ambiguity set therefore describes exactly the mixtures, with the regime weights, of one Wasserstein ball per regime. This is the regime decomposition used in the proof of Theorem 1 and in the coverage guarantee (Theorem 2).
--
--   **Formalization Note** The $\mathbb P_k$ range over all measures; $W_m(\mathbb P_k,\hat{\mathbb P}_k)\le\theta_k<\infty$ forces a coupling to exist and hence $\mathbb P_k$ to be a probability law.
--
--   Differences from the source:
--   - correction: display (9): 𝔼^P[ũ_k] ≤ θ_k for every k → Urs: 𝔼^P[ũ_k 1{k̃ = k}] ≤ w_kθ_k for every k; reason: the printed budget leaves ũ_k (k ≠ k̃) free and makes Theorem 1 false: K = 2, w = (½, ½), N₁ = N₂ = 1, I = 1, r₁₁ = r₁₂ = 0, θ = (1, 1); r̃ = −M, ũ = (M, 0) on k̃ = 1 and r̃ = 0, ũ = (−M, 0) on k̃ = 2 satisfy (9) for every M, so (11) = +∞ while (12) is finite; the corrected budget is the proof's own first display (p.ec2) and (EC.1)
--   - encoding: P[ñ = n | k̃ = k] = 1/N_k and P[k̃ = k] = w_k on ℝ^I × ℝ^K × [N_k]_{k=1}^K × [K] → P[k̃ = k, ñ = n] = w_k/N_k and P[k̃ = k] = w_k on (Fin I → ℝ) × (Fin K → ℝ) × (Fin K × ℕ); support ‖r̃ − r_{ñk̃}‖_m ≤ ũ_{k̃} a.s.; reason: the same laws (the joint masses sum to one, so ñ < N_{k̃} a.s.); the joint form is defined when w_k = 0
--   - encoding: standing assumptions of §3 (m ∈ [1,+∞], η ∈ (0,1), N_k sample counts, w_k regime probabilities, θ_k radii) → hypotheses 1 ≤ m, 0 < η < 1, 0 < N k, 0 ≤ w k, ∑ w = 1, 0 ≤ θ k; reason: the paper's setting, made explicit; no other hypothesis is added
--   - encoding: ℓm norm ‖·‖_m and conjugate norm ‖·‖_{m*} on ℝ^I → normM m (the PiLp m norm on Fin I → ℝ) and normM (ENNReal.conjExponent m); reason: Lean convention; ENNReal.conjExponent sends 1 ↦ ∞, 2 ↦ 2, ∞ ↦ 1, the Hölder conjugate
--   - encoding: W_m(P_k, P̂_k) ≤ θ_k with P_k a distribution → wassersteinM m (Pk k) (empiricalMeasure r k) ≤ ENNReal.ofReal (θ k), Pk k any measure; reason: a finite distance forces a coupling, so P_k is a probability law; W_m is an ℝ≥0∞ infimum of lower integrals
--   - encoding: regimes k ∈ [K], scenarios n ∈ [N_k], samples r_nk → k : Fin K, n : Fin (N k), r k n; reason: Lean convention; index i − 1 for paper index i
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, Lemma EC.1, display (EC.2), p.ec1

import Mathlib
import Definitions.Def_RegimeDRCVaR_Urs
import Definitions.Def_RegimeDRCVaR_empiricalMeasure
import Definitions.Def_RegimeDRCVaR_wassersteinM

open MeasureTheory
open scoped ENNReal

namespace RegimeDRCVaR

/-- **Lemma EC.1** (Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, p.ec1): "For all
θ = (θ₁, …, θ_K), we have: Π_r̃ U_rs(θ) = {P : P = ∑_{k∈[K]} w_k P_k, W_m(P_k, P̂_k) ≤ θ_k}, where
P̂_k = (1/N_k) ∑_{n∈[N_k]} δ_{r_nk}."

The laws of the return `r̃` under the members of `U_rs(θ)` are exactly the mixtures
`∑_k w_k P_k` of distributions `P_k` within ℓm-Wasserstein distance `θ_k` of the regime-`k`
empirical distribution.

**Formalization Note**
* `U_rs(θ)` carries the corrected regime budget `𝔼^P[ũ_k 1{k̃ = k}] ≤ w_kθ_k` (see `Urs`; the
  printed budget `𝔼^P[ũ_k] ≤ θ_k` makes Theorem 1 false).
* Standing assumptions of §3: `m ∈ [1, ∞]`, `N_k ≥ 1`, `w` a probability vector, `θ_k ≥ 0`
  (the radii of Wasserstein balls).
* The `P_k` are not required to be probability measures: `W_m(P_k, P̂_k) ≤ θ_k < ∞` forces a
  coupling to exist, and then `P_k` is the first marginal of a probability measure. -/
theorem lemma_EC1 {I K : ℕ} {N : Fin K → ℕ} (m : ℝ≥0∞) (hm : 1 ≤ m)
    (r : (k : Fin K) → Fin (N k) → Fin I → ℝ) (w θ : Fin K → ℝ)
    (hN : ∀ k, 0 < N k) (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) (hθ : ∀ k, 0 ≤ θ k) :
    {Q : Measure (Fin I → ℝ) | ∃ P ∈ Urs m r w θ, Q = P.map (fun ω => ω.1)} =
      {Q | ∃ Pk : Fin K → Measure (Fin I → ℝ),
        (∀ k, wassersteinM m (Pk k) (empiricalMeasure r k) ≤ ENNReal.ofReal (θ k)) ∧
        Q = ∑ k, ENNReal.ofReal (w k) • Pk k} := by sorry

end RegimeDRCVaR
