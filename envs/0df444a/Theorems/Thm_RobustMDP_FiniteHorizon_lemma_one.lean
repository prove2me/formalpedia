-- Prove2me | Theorems.Thm_RobustMDP_FiniteHorizon_lemma_one
-- name    : RobustMDP.FiniteHorizon.lemma_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:18:44.314901+00:00
-- url     : https://prove2.me/theorems/dcaf885b-7d88-4533-838d-cbe8b9e810fc
-- title:
--   Lemma 1, p. 783 — a monotone recursion solves the linear program (11)
-- statement:
--   Let $v_N\in\mathbb R^n$, $q\in\mathbb R^n_+$, and let $g_t:\mathbb R^n\to\mathbb R^n$, $t\in T=\{0,\dots,N-1\}$, be componentwise nondecreasing: $u\le v$ componentwise implies $g_t(u)\le g_t(v)$. Consider
--
--   $$
--   \eta:=\max_{v_0,\dots,v_{N-1}}\ q^{\mathsf T}v_0\quad\text{s.t.}\quad v_t\le g_t(v_{t+1}),\ t\in T, \tag{11}
--   $$
--
--   with inequalities componentwise and $v_N$ fixed. Then the recursion $v_t=g_t(v_{t+1})$, $t\in T$ (12), started at $v_N$, has a unique solution $v^*$; it is feasible for (11), and
--
--   $$
--   \eta=q^{\mathsf T}v_0^*=q^{\mathsf T}(g_0\circ g_1\circ\cdots\circ g_{N-1})(v_N),
--   $$
--
--   the maximum being attained at $v^*$.
--
--   The lemma turns every problem of the form (11) with monotone constraint maps into a backward recursion; the proof of Theorem 1 applies it to problems (14), (15) and (16).
--
--   **Formalization Note** Sequences $v_0,\dots,v_N$ are functions on `Fin (N+1)` with $v_N$ fixed. The paper writes the composition $g_1\circ\cdots\circ g_N$, an index slip for $T=\{0,\dots,N-1\}$; the Lean uses $g_0,\dots,g_{N-1}$, the composition being the fold of the list $[g_0,\dots,g_{N-1}]$ onto $v_N$. The maximum is stated with `IsGreatest`, so attainment is part of the claim.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 783, Lemma 1

import Mathlib

namespace RobustMDP.FiniteHorizon

/-- Lemma 1 (Nilim–El Ghaoui 2005, p. 783). Fix `v_N ∈ ℝⁿ`, `q ∈ ℝⁿ₊` and componentwise
nondecreasing maps `g_t : ℝⁿ → ℝⁿ`, `t ∈ T = {0, …, N-1}`. Consider problem (11): maximise
`qᵀ v_0` over `v_0, …, v_{N-1}` (with `v_N` fixed) subject to `v_t ≤ g_t(v_{t+1})` componentwise.
A vector sequence is encoded as `v : Fin (N+1) → Fin n → ℝ` with `v (Fin.last N) = v_N`.

Conclusions: the recursion (12) `v_t = g_t(v_{t+1})` with terminal value `v_N` has exactly one
solution `v*`; for it, `v*_0 = (g_0 ∘ ⋯ ∘ g_{N-1})(v_N)` (the list `[g_0, …, g_{N-1}]` folded
from the right onto `v_N`), `v*` is feasible, and `qᵀ v*_0` is the maximum of (11). The paper
writes the composition as `g_1 ∘ ⋯ ∘ g_N`, an index slip for `T = {0, …, N-1}`. -/
theorem lemma_one {n N : ℕ} (g : Fin N → (Fin n → ℝ) → (Fin n → ℝ))
    (hg : ∀ t, Monotone (g t)) (q : Fin n → ℝ) (hq : 0 ≤ q) (vN : Fin n → ℝ) :
    (∃! vstar : Fin (N + 1) → Fin n → ℝ,
        vstar (Fin.last N) = vN ∧ ∀ t : Fin N, vstar t.castSucc = g t (vstar t.succ)) ∧
    ∀ vstar : Fin (N + 1) → Fin n → ℝ,
      vstar (Fin.last N) = vN → (∀ t : Fin N, vstar t.castSucc = g t (vstar t.succ)) →
        vstar 0 = (List.ofFn g).foldr (fun f x => f x) vN ∧
        IsGreatest
          ((fun v : Fin (N + 1) → Fin n → ℝ => ∑ i, q i * v 0 i) ''
            {v | v (Fin.last N) = vN ∧ ∀ t : Fin N, v t.castSucc ≤ g t (v t.succ)})
          (∑ i, q i * vstar 0 i) := by sorry

end RobustMDP.FiniteHorizon
