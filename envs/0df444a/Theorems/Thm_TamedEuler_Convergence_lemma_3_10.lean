-- Prove2me | Theorems.Thm_TamedEuler_Convergence_lemma_3_10
-- name    : TamedEuler.Convergence.lemma_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:35.007752+00:00
-- url     : https://prove2.me/theorems/b47f0bae-42e5-40aa-ac92-8f10c83c4c52
-- title:
--   Lemma 3.10, p. 16 — uniformly bounded moments of µ(Y^N_n) and σ(Y^N_n)
-- statement:
--   In the standing setting of p. 2, let $Y^N_n$ be the tamed Euler approximations (8). Then
--   $$\sup_{N\in\mathbb N}\ \sup_{n\in\{0,1,\dots,N\}}\mathbb E\big[\|\mu(Y^N_n)\|^p\big]<\infty,\qquad \sup_{N\in\mathbb N}\ \sup_{n\in\{0,1,\dots,N\}}\mathbb E\big[\|\sigma(Y^N_n)\|^p\big]<\infty$$
--   for all $p\in[1,\infty)$, where $\|\sigma(\cdot)\|$ is the operator norm.
--
--   Together with Lemma 3.9 these bounds feed the error estimate of Theorem 1.1.
--
--   **Formalization Note** The two bounds of the lemma are one statement with one constant per $p$; expectations are $[0,\infty]$-valued.
-- source:
--   Hutzenthaler, Jentzen, Kloeden, arXiv:1010.3756v2, p. 16, Lemma 3.10

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_TamedEuler_Convergence_Setting
import Definitions.Def_TamedEuler_Convergence_Scheme

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace TamedEuler.Convergence

open EthierKurtz

/-- Hutzenthaler–Jentzen–Kloeden, arXiv:1010.3756v2, p. 16, Lemma 3.10:
`sup_{N ∈ ℕ} sup_{n ∈ {0,…,N}} 𝔼[‖µ(Y^N_n)‖^p] < ∞` and
`sup_{N ∈ ℕ} sup_{n ∈ {0,…,N}} 𝔼[‖σ(Y^N_n)‖^p] < ∞` (operator norm) for all `p ∈ [1, ∞)`. -/
theorem lemma_3_10 {d m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (c : ℝ)
    (W : ℝ≥0 → Ω → SDEState m) (ξ : Ω → SDEState d) (mu : SDEState d → SDEState d)
    (σ : SDEState d → Matrix (Fin d) (Fin m) ℝ)
    (h : Setting P ℱ T c W ξ mu σ) :
    ∀ p : ℝ, 1 ≤ p → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ N : ℕ, 1 ≤ N → ∀ n : ℕ, n ≤ N →
      ∫⁻ ω, ENNReal.ofReal (‖mu (Y T mu σ ξ W N n ω)‖ ^ p) ∂P ≤ C ∧
      ∫⁻ ω, ENNReal.ofReal (opNorm (σ (Y T mu σ ξ W N n ω)) ^ p) ∂P ≤ C := by sorry

end TamedEuler.Convergence
