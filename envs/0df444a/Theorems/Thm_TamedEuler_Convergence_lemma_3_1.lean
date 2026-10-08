-- Prove2me | Theorems.Thm_TamedEuler_Convergence_lemma_3_1
-- name    : TamedEuler.Convergence.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:43.090813+00:00
-- url     : https://prove2.me/theorems/af65ead3-1a5b-4c75-8e6b-ed062acd1a3c
-- title:
--   Lemma 3.1 (Dominator lemma), p. 15 — 𝟙_{Ω^N_n}‖Y^N_n‖ ≤ D^N_n
-- statement:
--   Assume the coefficient hypotheses of p. 2: $T>0$, $c>0$, $\mu$ continuously differentiable with $\|\mu'(x)\|\le c(1+\|x\|^c)$ and $\langle x-y,\mu(x)-\mu(y)\rangle\le c\|x-y\|^2$, and $\|\sigma(x)-\sigma(y)\|\le c\|x-y\|$ in the operator norm. Let $Y^N_n$ be the tamed Euler scheme (8), $D^N_n$ the dominating processes (13) and $\Omega^N_n$ the events (14). Then
--   $$\mathbb 1_{\Omega^N_n}\,\|Y^N_n\|\le D^N_n$$
--   for all $n\in\{0,1,\dots,N\}$ and all $N\in\mathbb N$.
--
--   This pathwise inequality, (15) of the introduction, is the main step towards the moment bounds of the scheme: on the events $\Omega^N_n$ the scheme cannot grow faster than the explicitly controlled processes $D^N_n$.
--
--   **Formalization Note** The inequality is stated for every $\omega$ (not almost surely), for an arbitrary path $W$ and an arbitrary initial value $\xi$: no probabilistic hypothesis is assumed, which is a stronger (still true) form of the lemma, since its proof uses none.
-- source:
--   Hutzenthaler, Jentzen, Kloeden, arXiv:1010.3756v2, p. 15, Lemma 3.1, (27)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_TamedEuler_Convergence_Setting
import Definitions.Def_TamedEuler_Convergence_Scheme
import Definitions.Def_TamedEuler_Convergence_Dominator

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace TamedEuler.Convergence

open EthierKurtz

/-- Hutzenthaler–Jentzen–Kloeden, arXiv:1010.3756v2, p. 15, Lemma 3.1 (Dominator lemma),
(27): `𝟙_{Ω^N_n} ‖Y^N_n‖ ≤ D^N_n` for all `n ∈ {0, …, N}` and `N ∈ ℕ`. Stated pathwise,
for every `ω` and for an arbitrary path `W` and initial value `ξ`: only the deterministic
coefficient hypotheses of the setting are assumed. -/
theorem lemma_3_1 {d m : ℕ} {Ω : Type*} (T : ℝ≥0) (c : ℝ)
    (mu : SDEState d → SDEState d) (σ : SDEState d → Matrix (Fin d) (Fin m) ℝ)
    (h : Coefficients d m T c mu σ)
    (W : ℝ≥0 → Ω → SDEState m) (ξ : Ω → SDEState d) :
    ∀ N : ℕ, 1 ≤ N → ∀ n : ℕ, n ≤ N → ∀ ω : Ω,
      (Good T c mu σ ξ W N n).indicator (fun ω => ‖Y T mu σ ξ W N n ω‖) ω
        ≤ D T c mu σ ξ W N n ω := by sorry

end TamedEuler.Convergence
