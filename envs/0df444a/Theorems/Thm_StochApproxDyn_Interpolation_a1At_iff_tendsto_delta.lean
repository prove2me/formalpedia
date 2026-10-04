-- Prove2me | Theorems.Thm_StochApproxDyn_Interpolation_a1At_iff_tendsto_delta
-- name    : StochApproxDyn.Interpolation.a1At_iff_tendsto_delta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:08:20.365141+00:00
-- url     : https://prove2.me/theorems/4628f111-25ba-4d57-a142-cba1cf14a7cc
-- title:
--   Proposition 4.1, A1 — the two forms of assumption A1 are equivalent
-- statement:
--   Let the step sizes satisfy $\gamma_n\ge0$, $\sum_n\gamma_n=\infty$, $\gamma_n\to0$, let $\{U_n\}_{n\ge1}$ be a sequence in $\mathbb R^d$, and let $\tau_n$, $m(t)$, $\overline U$ and $\Delta(t,T)=\sup_{0\le h\le T}\|\int_t^{t+h}\overline U(s)\,ds\|$ be as in §4.1. Then for every $T>0$,
--   $$\lim_{n\to\infty}\sup\Big\{\Big\|\sum_{i=n}^{k-1}\gamma_{i+1}U_{i+1}\Big\|:k=n+1,\dots,m(\tau_n+T)\Big\}=0\quad\Longleftrightarrow\quad\lim_{t\to\infty}\Delta(t,T)=0 .$$
--
--   The paper states assumption A1 in the discrete form and asserts that the continuous form is equivalent; Propositions 4.2 and 4.4 verify the discrete form, while the proof of Proposition 4.1 uses the continuous one.
--
--   **Formalization Note** The discrete form is written with $\varepsilon$: for all $\varepsilon>0$ there is $N$ such that the norm of every partial sum with $n\ge N$ and $n+1\le k\le m(\tau_n+T)$ is at most $\varepsilon$. The equivalence is stated for each fixed $T$.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 12, Proposition 4.1, assumption A1 ("or equivalently") and Eq. (10)

import Mathlib
import Definitions.Def_StochApproxDyn_Interpolation_Scheme

open scoped NNReal Topology
open Filter

namespace StochApproxDyn.Interpolation

/-- Benaïm 1999, Proposition 4.1, assumption A1, p. 12 ("or equivalently"): under the standing
assumptions on `γ`, for every `T > 0` the sum form of A1,
`lim_{n→∞} sup{‖Σ_{i=n}^{k−1} γ_{i+1} U_{i+1}‖ : k = n + 1, …, m(τ_n + T)} = 0`,
holds if and only if `lim_{t→∞} Δ(t, T) = 0`, where `Δ(t, T) = sup_{0≤h≤T} ‖∫_t^{t+h} Ū(s) ds‖`. -/
theorem a1At_iff_tendsto_delta {d : ℕ} (γ : ℕ → ℝ) (hγ : IsStepSizeSeq γ)
    (U : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℝ) (hT : 0 < T) :
    A1At γ U T ↔ Tendsto (fun t : ℝ => Delta γ U t T) atTop (𝓝 0) := by sorry

end StochApproxDyn.Interpolation
