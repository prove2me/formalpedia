-- Prove2me | Theorems.Thm_SennottDP_DiscountedASM_dc_of_atas_distinguished_state
-- name    : SennottDP.DiscountedASM.dc_of_atas_distinguished_state
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T07:56:35.860691+00:00
-- url     : https://prove2.me/theorems/391c268c-5600-4459-94d0-340f7edb7634
-- title:
--   Corollary 4.7.5 — ATAS sending excess probability to one state: DC($\alpha$) and the relative optimality equation
-- statement:
--   Let $\Delta$ be an MDC with countable state space and $\alpha\in(0,1)$, and assume $V_\alpha(i)<\infty$ for every state $i$. Let $(\Delta_N)_{N\ge N_0}$ be an ATAS for $\Delta$ that sends all excess probability to a distinguished state $z$, with $z\in S_N$ for $N\ge N_0$. Then:
--
--   1. Assumption DC($\alpha$) holds.
--   2. For $N\ge N_0$ the values $V^N_\alpha(j)$, $j\in S_N$, are finite, and with the relative value function $R^N_\alpha=V^N_\alpha-V^N_\alpha(z)$ the discount optimality equation of $\Delta_N$ takes the form
--   $$
--   V^N_\alpha(i)=\alpha V^N_\alpha(z)+\min_{a\in A_i}\Big\{C(i,a)+\alpha\sum_{j\in S_N}P_{ij}(a)\,R^N_\alpha(j)\Big\},\qquad i\in S_N.
--   $$
--
--   Note that the original transition probabilities $P_{ij}(a)$ of $\Delta$ appear, not those of $\Delta_N$. This form is used for computation in the inventory model of Chapter 5.
--
--   **Formalization Note** The book assumes, without loss of generality, that $N_0$ is large enough that $S_N$ contains $z$; this is the hypothesis $z\in S_N$ for $N\ge N_0$. The equation is stated in real numbers via `ENNReal.toReal`, together with the finiteness of $V^N_\alpha$ on $S_N$, so that the relative value function is an honest difference.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 80–81, Corollary 4.7.5, equation (4.53); p. 30 (distinguished state)

import Mathlib
import Definitions.Def_SennottDP_DiscountedASM_MDC
import Definitions.Def_SennottDP_DiscountedASM_ApproxSeq

open scoped ENNReal NNReal
open Classical Filter Topology

namespace SennottDP.DiscountedASM

/-- Corollary 4.7.5 (pp. 80–81): if `V_α < ∞` and `(Δ_N)` is an ATAS sending the excess
probability to a distinguished state `z` (with `z ∈ S_N` for `N ≥ N₀`), then DC(α) holds, and,
with the relative value function `R^N_α = V^N_α - V^N_α(z)` (the `V^N_α` being finite), the
discount optimality equation of `Δ_N` is
`V^N_α(i) = α V^N_α(z) + min_a {C(i,a) + α Σ_{j ∈ S_N} P_{ij}(a) R^N_α(j)}`, `i ∈ S_N` (4.53). -/
theorem dc_of_atas_distinguished_state {S Act : Type} [Countable S] (M : MDC S Act)
    (Δs : ApproxSeq M) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1)
    (hV : ∀ i, M.value α i < ⊤)
    (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : Δs.IsATAS q)
    (z : S) (hz : ∀ N, Δs.N0 ≤ N → z ∈ Δs.SN N) (hqz : Δs.SendsExcessTo q {z}) :
    Δs.DC α ∧
    ∀ N, Δs.N0 ≤ N → (∀ j ∈ Δs.SN N, Δs.VN α N j < ⊤) ∧
      ∀ i ∈ Δs.SN N,
        (Δs.VN α N i).toReal =
          (α : ℝ) * (Δs.VN α N z).toReal +
            (M.A i).inf' (M.A_nonempty i) (fun a => (M.C i a : ℝ) +
              (α : ℝ) * ∑ j ∈ Δs.SN N,
                (M.P i a j).toReal * ((Δs.VN α N j).toReal - (Δs.VN α N z).toReal)) := by sorry

end SennottDP.DiscountedASM
