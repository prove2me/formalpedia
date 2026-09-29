-- Prove2me | Theorems.Thm_RobustMDP_EntropyInner_whole_simplex
-- name    : RobustMDP.EntropyInner.whole_simplex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:29:38.592619+00:00
-- url     : https://prove2.me/theorems/6293ac09-a603-4327-8332-53abe4d910b4
-- title:
--   §6.1, p. 791 — for $\beta\ge\max_i(-\log q_i)$ the entropy set is the whole simplex and the worst case is $v_{\max}$
-- statement:
--   Let $q\in\Delta_n$ with $q(j)>0$ for all $j$, let $\beta>0$ and $v\in\mathbb R^n$. Let $\mathcal P=\{p\in\Delta_n : D(p\|q)\le\beta\}$.
--
--   1. The quantity $\max_i(-\log q_i)$ is the maximum of the relative entropy over the simplex:
--   $$
--   \max_{p\in\Delta_n} D(p\|q) = \max_i(-\log q_i),
--   $$
--   and the maximum is attained.
--   2. If $\beta\ge\max_i(-\log q_i)$, then $\mathcal P=\Delta_n$ and the worst-case value of $p^{\mathsf T}v$ over $\mathcal P$ is
--   $$
--   \max_{p\in\mathcal P} p^{\mathsf T}v = v_{\max} := \max_j v(j),
--   $$
--   again attained.
--
--   This identifies the regime in which the entropy constraint is inactive and the robust inner problem ignores the nominal distribution $q$.
--
--   **Formalization Note** Both maxima are stated with `IsGreatest` (the value lies in the image and bounds it from above); $\max_i(-\log q_i)$ is the indexed supremum `⨆ i, -Real.log (q i)` over the finite index set.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 791, §6.1, last paragraph

import Mathlib
import Definitions.Def_RobustMDP_EntropyInner_klBall
import Definitions.Def_RobustMDP_EntropyInner_dualFunction

namespace RobustMDP.EntropyInner

/-- §6.1 (Nilim–El Ghaoui 2005, p. 791). Let `q ∈ Δₙ` with `q > 0` and `β > 0`.
(a) `maxᵢ (−log qᵢ)` is the maximum of `p ↦ D(p‖q)` over the simplex `Δₙ` (attained).
(b) If `β ≥ maxᵢ (−log qᵢ)`, the entropy set `𝒫 = {p ∈ Δₙ : D(p‖q) ≤ β}` is the whole simplex, and
the worst-case value of `pᵀv` over `𝒫` is `v_max = maxⱼ v(j)` (attained). -/
theorem whole_simplex {n : ℕ} (q v : Fin n → ℝ) (β : ℝ)
    (hq : q ∈ stdSimplex ℝ (Fin n)) (hq_pos : ∀ j, 0 < q j) (hβ : 0 < β) :
    IsGreatest ((fun p => klDiv p q) '' stdSimplex ℝ (Fin n)) (⨆ i, -Real.log (q i)) ∧
    ((⨆ i, -Real.log (q i)) ≤ β →
      klBall q β = stdSimplex ℝ (Fin n) ∧
      IsGreatest ((fun p : Fin n → ℝ => ∑ j, p j * v j) '' klBall q β) (vmax v)) := by sorry

end RobustMDP.EntropyInner
