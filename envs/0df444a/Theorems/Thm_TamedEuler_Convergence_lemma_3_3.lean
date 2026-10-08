-- Prove2me | Theorems.Thm_TamedEuler_Convergence_lemma_3_3
-- name    : TamedEuler.Convergence.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:51.111987+00:00
-- url     : https://prove2.me/theorems/7a8fc8ae-0abe-49cf-a074-0a059cbcfcba
-- title:
--   Lemma 3.3, p. 15 — sup over N ≥ 4λpT of 𝔼[exp(pλ Σ_{k<N} ‖ΔW^N_k‖²)] is finite
-- statement:
--   In the standing setting of p. 2, with $\lambda=(1+2c+T+\|\mu(0)\|+\|\sigma(0)\|)^4$ and $\Delta W^N_k=W_{(k+1)T/N}-W_{kT/N}$,
--   $$\sup_{\substack{N\in\mathbb N\\ N\ge4\lambda pT}}\ \mathbb E\Big[\exp\Big(p\lambda\sum_{k=0}^{N-1}\|\Delta W^N_k\|^2\Big)\Big]<\infty$$
--   for all $p\in[1,\infty)$.
--
--   It controls the quadratic part of the exponent of the dominating processes $D^N_n$ (Lemma 3.5).
--
--   **Formalization Note** For each $p\ge1$ there is a finite $C\in[0,\infty]$ bounding the expectation (a $[0,\infty]$-valued integral) for every $N\ge1$ with $N\ge4\lambda pT$.
-- source:
--   Hutzenthaler, Jentzen, Kloeden, arXiv:1010.3756v2, p. 15, Lemma 3.3, (29)

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

/-- Hutzenthaler–Jentzen–Kloeden, arXiv:1010.3756v2, p. 15, Lemma 3.3, (29):
`sup_{N ∈ ℕ, N ≥ 4λpT} 𝔼[exp(pλ Σ_{k=0}^{N−1} ‖ΔW^N_k‖²)] < ∞` for all `p ∈ [1, ∞)`. -/
theorem lemma_3_3 {d m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (c : ℝ)
    (W : ℝ≥0 → Ω → SDEState m) (ξ : Ω → SDEState d) (mu : SDEState d → SDEState d)
    (σ : SDEState d → Matrix (Fin d) (Fin m) ℝ)
    (h : Setting P ℱ T c W ξ mu σ) :
    ∀ p : ℝ, 1 ≤ p → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ N : ℕ, 1 ≤ N →
      4 * lam T c mu σ * p * T ≤ (N : ℝ) →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (p * lam T c mu σ *
          ∑ k ∈ Finset.range N, ‖dW T W N k ω‖ ^ 2)) ∂P ≤ C := by sorry

end TamedEuler.Convergence
