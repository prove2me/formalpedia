-- Prove2me | Theorems.Thm_PolyEulerFlow_lemma_31
-- name    : PolyEulerFlow.lemma_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:11.082313+00:00
-- url     : https://prove2.me/theorems/3b699017-e1d6-42ff-99e8-5e25fd16a19e
-- title:
--   Lemma 31 — the uniform clock
-- statement:
--   There are absolute constants $A_0,B_0,C_{dur},C_{env},D_{clk}>0$, a constant $C_{next}>0$ and $\varepsilon_0>0$ such that the following holds for $0<\varepsilon\le\varepsilon_0$, $0\le\nu\le\varepsilon^2$ and every mesh. Let $L=\log(1/\varepsilon)$, $\mu_0=\varepsilon^{1/4}$, $\lambda_{clk}=3/8$. Run the autonomous clock $(p,\tau)$ of §6.3 with disturbances of level $\nu$, from a state of the scalar box satisfying the entry conditions of phase $j$,
--   $$p_j\ge9/10,\quad|p_{j+1}|,|p_{j+2}|\le\mu_0,\quad\varepsilon/2\le\tau_j\le A_0\varepsilon,\quad\tau_{j+1}\le2\varepsilon,\quad\tau_{j+2}\le B_0\varepsilon^{4/5},\tag{29}$$
--   at time $t_j=0$. Let $t_{j+1}$ be the first subsequent grid time with $p_{j+1}\ge9/10$ and $t^b_j$ the first grid time after $t_j$ with $\tau_j\ge1/4$. Then both exist and:
--
--   1. the entry conditions (29) hold at $t_{j+1}$ with $j$ replaced by $j+1$;
--   2. $L-C_{dur}\le t^b_j-t_j\le4L+C_{dur}$ and $0\le t_{j+1}-t^b_j\le D_{clk}$ (30);
--   3. $p_j\ge9/10$ at every grid time up to $t_{j+1}-D_{clk}$, and $\tau_{j+1}\le C_{next}\varepsilon$ during the whole phase;
--   4. at every grid time of $[t_j,t_{j+1}]$: $|p_{j-1}(t)|\le C_{env}e^{-\lambda_{clk}(t-t_j)}+C_{env}\varepsilon^{37/20}+C_{env}\nu$ and $|p_{j+2}(t)|\le C_{env}\mu_0$ (31);
--   5. before $t^b_j$: $|p_{j+1}(t)|\le C_{env}(\mu_0+\tau_j(t)^4+\nu)$ and $\tau_j(t)\le C_{env}\varepsilon e^{(1+4\nu)(t-t_j)}$ (32).
--
--   The initial clock $p=(1,0,0,0)$, $\tau_i=\varepsilon$ satisfies (29) for phase $0$. The lemma is the induction step that keeps the four-phase clock running forever with phases of length $\Theta(L)$, uniformly in the mesh and under perturbation.
--
--   Differences from the source:
--   - generalization: every mesh 0 < η ≤ 1 (one constant step) → every variable mesh 0 < η_k ≤ 1 with Σ η_k = ∞; reason: Corollary 39 (p.34) states that every clock, cut and cycle estimate holds on such meshes; every constant step in (0, 1] is one of them
--   - reading: (29) are mapped to the same conditions with j replaced by j + 1 → the next phase entry t_{j+1} exists and (29) holds there for j + 1; reason: this is the induction the lemma is used for
--   - reading: the active bit is at least 9/10 outside a terminal interval of length at most D_clk → p_j ≥ 9/10 at every grid time t_k ≤ t_{j+1} − D_clk of the phase; reason: the terminal interval is [t_{j+1} − D_clk, t_{j+1}]
--   - reading: the next timer remains O(ε) during the whole phase → τ_{j+1} ≤ C_next ε at every grid time of [t_j, t_{j+1}], with C_next existential with the other constants; reason: O(ε) with a constant fixed with the lemma's constants
--   - encoding: a phase starting at t_j → a clock orbit started at index 0 (t_j = 0) with the shifted mesh and disturbances; reason: the scheme is autonomous, so a phase starting later is the orbit of the shifted data
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), Lemma 31, p.30 (PDF 32), with t_j, t^b_j defined on p.29 (PDF 31)

import Mathlib
import Definitions.Def_PolyEulerFlow_IsUniformClock

namespace PolyEulerFlow

/-- **Lemma 31 (Uniform clock)**, p.30 (PDF 32). Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript,
sha256 c4e01b2b…).

There are absolute constants `A₀, B₀, C_dur, C_env, D_clk > 0`, a constant for "the next timer remains `O(ε)`", and `ε₀ > 0` such that, for
`0 < ε ≤ ε₀`, `0 ≤ ν ≤ ε²` and every mesh, the autonomous clock `(p, τ)` of §6.3, started in the scalar box at the entry conditions (29) of phase `j`,
reaches the entry conditions of phase `j + 1` at its next phase entry, with the duration bounds (30), the bound on the active bit, the bound on
the next timer, the envelopes (31) on the closed phase and (32) before `t^b_j`; and the initial clock `p = (1, 0, 0, 0)`, `τ_i = ε` satisfies (29) at
phase `0`. See `IsUniformClock`.

**Formalization Note** The mesh is variable (`0 < η_k ≤ 1`, `Σ η_k = ∞`), as Corollary 39 (p.34) asserts for every clock estimate; a constant mesh
`0 < η ≤ 1` is the special case. Phase `j` starts at index `0`, with `t_j = 0`. -/
theorem lemma_31 :
    ∃ A0 B0 Cdur Cenv Cnext Dclk ε0 : ℝ, IsUniformClock A0 B0 Cdur Cenv Cnext Dclk ε0 := by sorry

end PolyEulerFlow
