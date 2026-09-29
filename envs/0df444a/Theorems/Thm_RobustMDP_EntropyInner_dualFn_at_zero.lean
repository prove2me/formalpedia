-- Prove2me | Theorems.Thm_RobustMDP_EntropyInner_dualFn_at_zero
-- name    : RobustMDP.EntropyInner.dualFn_at_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:32:00.000523+00:00
-- url     : https://prove2.me/theorems/fc18f597-8b00-4811-82b6-ecda9391b6db
-- title:
--   Eq. (49), p. 791 — $\sigma(\lambda)=v_{\max}+(\beta+\log Q(v))\lambda+o(\lambda)$ as $\lambda\to0^+$
-- statement:
--   Let $q\in\Delta_n$ with $q(j)>0$ for all $j$, let $\beta>0$ and $v\in\mathbb R^n$, and let $\sigma$ be the dual function (47). Write $v_{\max}=\max_j v(j)$ and $Q(v)=\sum_{j:\,v(j)=v_{\max}}q(j)$. Then, as $\lambda\to 0^+$,
--
--   $$
--   \sigma(\lambda)=v_{\max}+(\beta+\log Q(v))\lambda+o(\lambda).
--   $$
--
--   In particular $\sigma(\lambda)\to v_{\max}$, which is the paper's $\sigma(0)=v_{\max}$, and the right derivative of $\sigma$ at $0$ is $\sigma'(0)=\beta+\log Q(v)$.
--
--   The expansion at $0$ decides whether the minimum of $\sigma$ is attained at an interior $\lambda$ or only in the limit $\lambda\to0^+$.
--
--   **Formalization Note** The statement has two parts: `Tendsto` of $\sigma$ to $v_{\max}$ along `𝓝[>] 0`, and the remainder $\sigma(\lambda)-v_{\max}-(\beta+\log Q(v))\lambda$ is little-o of $\lambda$ along `𝓝[>] 0`. Appendix C in fact shows the remainder is $O(\lambda e^{-t/\lambda})$ for some $t>0$; the statement here is the printed $o(\lambda)$.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 791, §6.3, Eq. (49) and the definition of Q(v); proof in Appendix C, p. 797

import Mathlib
import Definitions.Def_RobustMDP_EntropyInner_dualFunction
open Filter Topology

namespace RobustMDP.EntropyInner

/-- Eq. (49) (Nilim–El Ghaoui 2005, §6.3, p. 791; proof in Appendix C, p. 797). For `q ∈ Δₙ` with
`q > 0` and `β > 0`, as `λ → 0⁺`,
`σ(λ) = v_max + (β + log Q(v)) λ + o(λ)`, where `Q(v) = ∑_{j : v(j) = v_max} q(j)`. In particular
`σ(λ) → v_max` (the paper's `σ(0) = v_max`). -/
theorem dualFn_at_zero {n : ℕ} (q v : Fin n → ℝ) (β : ℝ)
    (hq : q ∈ stdSimplex ℝ (Fin n)) (hq_pos : ∀ j, 0 < q j) (hβ : 0 < β) :
    Tendsto (fun lam => dualFn q v β lam) (𝓝[>] 0) (𝓝 (vmax v)) ∧
    (fun lam => dualFn q v β lam - vmax v - (β + Real.log (maxMass q v)) * lam)
      =o[𝓝[>] 0] (fun lam : ℝ => lam) := by sorry

end RobustMDP.EntropyInner
