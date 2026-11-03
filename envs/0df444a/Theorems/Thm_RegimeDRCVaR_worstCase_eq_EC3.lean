-- Prove2me | Theorems.Thm_RegimeDRCVaR_worstCase_eq_EC3
-- name    : RegimeDRCVaR.worstCase_eq_EC3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:25:31.3536+00:00
-- url     : https://prove2.me/theorems/4e8121c7-5938-4415-bdeb-f321d822445f
-- title:
--   Proof of Theorem 1 — the worst-case expected loss over $\mathcal U_{rs}(\boldsymbol\theta)$ equals the dual (EC.3) (corrected: regime budget of (9))
-- statement:
--   In the setting of Theorem 1 ($m\in[1,+\infty]$, $N_k\ge1$, $w$ a probability vector, $\theta_k\ge0$), for every portfolio $x\in\mathbb R^I$ and every $v\in\mathbb R$,
--   $$
--   \sup_{\mathbb P\in\mathcal U_{rs}(\boldsymbol\theta)}\mathbb E^{\mathbb P}[G(x,\tilde r)]
--   =\inf_{\boldsymbol\alpha,\boldsymbol\beta}\Big\{\sum_{k\in[K]}\sum_{n\in[N_k]}\frac{w_k}{N_k}\alpha_{nk}+\sum_{k\in[K]}\beta_kw_k\theta_k\Big\}
--   $$
--   where the infimum is over the $(\boldsymbol\alpha,\boldsymbol\beta)$ with
--
--   1. $\alpha_{nk}+\beta_ku\ge-x'r-v$ for all $k,n$, $r\in\mathbb R^I$ and $u$ with $\rho(r,r_{nk})\le u$;
--   2. $\alpha_{nk}+\beta_ku\ge0$ for the same $k,n,r,u$;
--   3. $\beta_k\ge0$ for all $k$.
--
--   This is strong duality for the worst-case expectation: the infinite-dimensional supremum over laws becomes a semi-infinite linear program in finitely many multipliers.
--
--   Differences from the source:
--   - correction: display (9): 𝔼^P[ũ_k] ≤ θ_k for every k → Urs: 𝔼^P[ũ_k 1{k̃ = k}] ≤ w_kθ_k for every k; reason: the printed budget leaves ũ_k (k ≠ k̃) free and makes Theorem 1 false: K = 2, w = (½, ½), N₁ = N₂ = 1, I = 1, r₁₁ = r₁₂ = 0, θ = (1, 1); r̃ = −M, ũ = (M, 0) on k̃ = 1 and r̃ = 0, ũ = (−M, 0) on k̃ = 2 satisfy (9) for every M, so (11) = +∞ while (12) is finite; the corrected budget is the proof's own first display (p.ec2) and (EC.1)
--   - encoding: P[ñ = n | k̃ = k] = 1/N_k and P[k̃ = k] = w_k on ℝ^I × ℝ^K × [N_k]_{k=1}^K × [K] → P[k̃ = k, ñ = n] = w_k/N_k and P[k̃ = k] = w_k on (Fin I → ℝ) × (Fin K → ℝ) × (Fin K × ℕ); support ‖r̃ − r_{ñk̃}‖_m ≤ ũ_{k̃} a.s.; reason: the same laws (the joint masses sum to one, so ñ < N_{k̃} a.s.); the joint form is defined when w_k = 0
--   - encoding: standing assumptions of §3 (m ∈ [1,+∞], η ∈ (0,1), N_k sample counts, w_k regime probabilities, θ_k radii) → hypotheses 1 ≤ m, 0 < η < 1, 0 < N k, 0 ≤ w k, ∑ w = 1, 0 ≤ θ k; reason: the paper's setting, made explicit; no other hypothesis is added
--   - encoding: ℓm norm ‖·‖_m and conjugate norm ‖·‖_{m*} on ℝ^I → normM m (the PiLp m norm on Fin I → ℝ) and normM (ENNReal.conjExponent m); reason: Lean convention; ENNReal.conjExponent sends 1 ↦ ∞, 2 ↦ 2, ∞ ↦ 1, the Hölder conjugate
--   - encoding: sup and min of real-valued problems → worst case as an ℝ≥0∞ supremum of lower integrals; objectives of (11) and optimal values as EReal infima; reason: Lean convention; the loss is nonnegative and the values are finite on every instance where the source's are, ±∞ otherwise
--   - encoding: regimes k ∈ [K], scenarios n ∈ [N_k], samples r_nk → k : Fin K, n : Fin (N k), r k n; reason: Lean convention; index i − 1 for paper index i
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, proof of Theorem 1, display (EC.3), p.ec2

import Mathlib
import Definitions.Def_RegimeDRCVaR_worstCase
import Definitions.Def_RegimeDRCVaR_feasEC3
import Definitions.Def_RegimeDRCVaR_objEC3

open MeasureTheory
open scoped ENNReal

namespace RegimeDRCVaR

/-- **Proof of Theorem 1, the dual problem (EC.3)** (Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930,
p.ec2): for every portfolio `x` and level `v`,
`sup_{P ∈ U_rs(θ)} 𝔼^P[G(x, r)]` equals the optimal value of
`inf_{α,β} ∑_k ∑_n (w_k/N_k) α_{nk} + ∑_k β_k w_kθ_k` subject to
`α_{nk} + β_k u_k ≥ −x′r − v` and `α_{nk} + β_k u_k ≥ 0` for all `k, n`, `r ∈ ℝ^I` with
`ρ(r, r_{nk}) ≤ u_k`, and `β_k ≥ 0`.

**Formalization Note**
* `U_rs(θ)` carries the corrected regime budget `𝔼^P[ũ_k 1{k̃ = k}] ≤ w_kθ_k` (the first
  display of this proof); with the printed (9) the left side is `+∞`.
* The worst case is an `ℝ≥0∞` supremum coerced to `EReal`; the infimum of (EC.3) is in `EReal`.
* Standing assumptions of §3: `m ∈ [1, ∞]`, `N_k ≥ 1`, `w` a probability vector, `θ_k ≥ 0`.
  `x ∈ ℝ^I` is arbitrary (membership in `𝒳` plays no role at fixed `x`). -/
theorem worstCase_eq_EC3 {I K : ℕ} {N : Fin K → ℕ} (m : ℝ≥0∞) (hm : 1 ≤ m)
    (r : (k : Fin K) → Fin (N k) → Fin I → ℝ) (w θ : Fin K → ℝ)
    (hN : ∀ k, 0 < N k) (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) (hθ : ∀ k, 0 ≤ θ k)
    (x : Fin I → ℝ) (v : ℝ) :
    ((worstCase m r w θ x v : ℝ≥0∞) : EReal) =
      ⨅ (α : (k : Fin K) → Fin (N k) → ℝ) (β : Fin K → ℝ) (_ : feasEC3 m r x v α β),
        ((objEC3 w θ α β : ℝ) : EReal) := by sorry

end RegimeDRCVaR
