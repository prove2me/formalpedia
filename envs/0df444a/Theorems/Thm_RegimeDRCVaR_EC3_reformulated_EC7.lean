-- Prove2me | Theorems.Thm_RegimeDRCVaR_EC3_reformulated_EC7
-- name    : RegimeDRCVaR.EC3_reformulated_EC7
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:27:11.137286+00:00
-- url     : https://prove2.me/theorems/a0de1713-ccd4-432f-8ec9-0c879815602b
-- title:
--   Proof of Theorem 1 — the constraints of (EC.3) are those of (EC.7), and (11) equals (EC.7) (corrected: regime budget of (9))
-- statement:
--   In the setting of Theorem 1 ($m\in[1,+\infty]$, $\eta\in(0,1)$, $N_k\ge1$, $w$ a probability vector, $\theta_k\ge0$, $\mathcal X=\{x\mid Ax=b,\ Cx\ge d\}$):
--
--   1. for every $x$, $v$, $\boldsymbol\alpha$, $\boldsymbol\beta$, the semi-infinite constraints of (EC.3) hold iff
--   $$
--   r_{nk}'x\ge-\alpha_{nk}-v,\qquad \beta_k\ge\|x\|_{m^*},\qquad \alpha_{nk}\ge0\qquad(\forall k,n);
--   $$
--   2. the optimal value of (11) equals the optimal value of
--   $$
--   \min_{v,x,\boldsymbol\alpha,\boldsymbol\beta}\ v+\frac1{1-\eta}\Big[\sum_{k\in[K]}\sum_{n\in[N_k]}\frac{w_k}{N_k}\alpha_{nk}+\sum_{k\in[K]}\beta_kw_k\theta_k\Big]
--   \ \text{ s.t. the constraints above and } x\in\mathcal X. \tag{EC.7}
--   $$
--
--   This is the step that makes the dual finite: one linear constraint per sample and one norm constraint per regime.
--
--   Differences from the source:
--   - correction: display (9): 𝔼^P[ũ_k] ≤ θ_k for every k → Urs: 𝔼^P[ũ_k 1{k̃ = k}] ≤ w_kθ_k for every k; reason: the printed budget leaves ũ_k (k ≠ k̃) free and makes Theorem 1 false: K = 2, w = (½, ½), N₁ = N₂ = 1, I = 1, r₁₁ = r₁₂ = 0, θ = (1, 1); r̃ = −M, ũ = (M, 0) on k̃ = 1 and r̃ = 0, ũ = (−M, 0) on k̃ = 2 satisfy (9) for every M, so (11) = +∞ while (12) is finite; the corrected budget is the proof's own first display (p.ec2) and (EC.1)
--   - encoding: P[ñ = n | k̃ = k] = 1/N_k and P[k̃ = k] = w_k on ℝ^I × ℝ^K × [N_k]_{k=1}^K × [K] → P[k̃ = k, ñ = n] = w_k/N_k and P[k̃ = k] = w_k on (Fin I → ℝ) × (Fin K → ℝ) × (Fin K × ℕ); support ‖r̃ − r_{ñk̃}‖_m ≤ ũ_{k̃} a.s.; reason: the same laws (the joint masses sum to one, so ñ < N_{k̃} a.s.); the joint form is defined when w_k = 0
--   - encoding: standing assumptions of §3 (m ∈ [1,+∞], η ∈ (0,1), N_k sample counts, w_k regime probabilities, θ_k radii) → hypotheses 1 ≤ m, 0 < η < 1, 0 < N k, 0 ≤ w k, ∑ w = 1, 0 ≤ θ k; reason: the paper's setting, made explicit; no other hypothesis is added
--   - encoding: ℓm norm ‖·‖_m and conjugate norm ‖·‖_{m*} on ℝ^I → normM m (the PiLp m norm on Fin I → ℝ) and normM (ENNReal.conjExponent m); reason: Lean convention; ENNReal.conjExponent sends 1 ↦ ∞, 2 ↦ 2, ∞ ↦ 1, the Hölder conjugate
--   - encoding: sup and min of real-valued problems → worst case as an ℝ≥0∞ supremum of lower integrals; objectives of (11) and optimal values as EReal infima; reason: Lean convention; the loss is nonnegative and the values are finite on every instance where the source's are, ±∞ otherwise
--   - encoding: regimes k ∈ [K], scenarios n ∈ [N_k], samples r_nk → k : Fin K, n : Fin (N k), r k n; reason: Lean convention; index i − 1 for paper index i
--   - reading: Combining all the reformulated constraint in (EC.3), we obtain the following LP: (EC.7) → clause 1: feasEC3 ↔ the finite constraints of (EC.7); clause 2: val11 = valEC7; reason: the sentence asserts that (11) becomes (EC.7) after the constraints of (EC.3) are rewritten; 'LP' is loose wording, (EC.7) is a convex program for general m
--   - generalization: 𝒳 = {x | Ax = b, Cx ≥ d} with the budget constraint 1′x = 1 embedded in it as a necessary constraint (p.9) → feasX A b C d for arbitrary A, b, C, d (no budget row required); reason: the argument never uses the budget row; the source’s 𝒳 is the instance in which one row of (A, b) is (1′, 1)
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, proof of Theorem 1, display (EC.7), p.ec3

import Mathlib
import Definitions.Def_RegimeDRCVaR_feasEC3
import Definitions.Def_RegimeDRCVaR_val11
import Definitions.Def_RegimeDRCVaR_valEC7

open Matrix
open scoped ENNReal

namespace RegimeDRCVaR

/-- **Proof of Theorem 1, from (EC.3) to (EC.7)** (Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, p.ec3):
"Combining all the reformulated constraint in (EC.3), we obtain the following LP:
`min_{v,x,α,β} v + 1/(1−η) [∑_k ∑_n (w_k/N_k) α_{nk} + ∑_k β_k w_kθ_k]` s.t.
`r′_{nk}x ≥ −α_{nk} − v`, `β_k ≥ ‖x‖_{m*}` for all `k`, `α_{nk} ≥ 0`, `x ∈ 𝒳`   (EC.7)."

Two statements:
1. the semi-infinite constraints of (EC.3) at `(x, v)` hold iff the finite constraints
   `r′_{nk}x ≥ −α_{nk} − v`, `β_k ≥ ‖x‖_{m*}` and `α_{nk} ≥ 0` of (EC.7) hold;
2. the optimal value of problem (11) equals the optimal value of (EC.7).

**Formalization Note**
* (11) uses `U_rs(θ)` with the corrected regime budget `𝔼^P[ũ_k 1{k̃ = k}] ≤ w_kθ_k` (see `Urs`).
* "LP" is the paper's wording; for general `m` (EC.7) is a convex program, and the claim
  formalized is that (11) becomes (EC.7).
* Standing assumptions of §3: `m ∈ [1, ∞]`, `η ∈ (0, 1)`, `N_k ≥ 1`, `w` a probability vector,
  `θ_k ≥ 0`. Optimal values are `EReal` infima. -/
theorem EC3_reformulated_EC7 {I K p q : ℕ} {N : Fin K → ℕ} (m : ℝ≥0∞) (hm : 1 ≤ m)
    (r : (k : Fin K) → Fin (N k) → Fin I → ℝ) (w θ : Fin K → ℝ) (η : ℝ)
    (hN : ∀ k, 0 < N k) (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) (hθ : ∀ k, 0 ≤ θ k)
    (hη0 : 0 < η) (hη1 : η < 1)
    (A : Matrix (Fin p) (Fin I) ℝ) (b : Fin p → ℝ) (C : Matrix (Fin q) (Fin I) ℝ)
    (d : Fin q → ℝ) :
    (∀ (x : Fin I → ℝ) (v : ℝ) (α : (k : Fin K) → Fin (N k) → ℝ) (β : Fin K → ℝ),
      feasEC3 m r x v α β ↔
        ((∀ k n, -(α k n) - v ≤ r k n ⬝ᵥ x) ∧
          (∀ k, normM (ENNReal.conjExponent m) x ≤ β k) ∧ (∀ k n, 0 ≤ α k n))) ∧
    val11 m r w θ η A b C d = valEC7 m r w θ η A b C d := by sorry

end RegimeDRCVaR
