-- Prove2me | Theorems.Thm_TamedEuler_Convergence_lemma_3_5
-- name    : TamedEuler.Convergence.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:04.341021+00:00
-- url     : https://prove2.me/theorems/51a12290-6d47-44b6-abcd-beb2c24ce4ac
-- title:
--   Lemma 3.5, p. 15 — uniformly bounded moments of the dominating processes, N ≥ 8λpT
-- statement:
--   In the standing setting of p. 2, let $D^N_n$ be the dominating stochastic processes (13). Then
--   $$\sup_{\substack{N\in\mathbb N\\ N\ge8\lambda pT}}\ \mathbb E\Big[\sup_{n\in\{0,1,\dots,N\}}|D^N_n|^p\Big]<\infty$$
--   for all $p\in[1,\infty)$.
--
--   Combined with the dominator lemma (Lemma 3.1) it bounds the moments of the scheme on the events $\Omega^N_n$.
--
--   **Formalization Note** For each $p\ge1$ one finite constant bounds the expectation (a $[0,\infty]$-valued integral of the finite maximum over $n\le N$) for every $N\ge1$ with $N\ge8\lambda pT$.
-- source:
--   Hutzenthaler, Jentzen, Kloeden, arXiv:1010.3756v2, p. 15, Lemma 3.5, (31)

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

/-- Hutzenthaler–Jentzen–Kloeden, arXiv:1010.3756v2, p. 15, Lemma 3.5 (Uniformly bounded
moments of the dominating stochastic processes), (31):
`sup_{N ∈ ℕ, N ≥ 8λpT} 𝔼[sup_{n ∈ {0,…,N}} |D^N_n|^p] < ∞` for all `p ∈ [1, ∞)`. -/
theorem lemma_3_5 {d m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (c : ℝ)
    (W : ℝ≥0 → Ω → SDEState m) (ξ : Ω → SDEState d) (mu : SDEState d → SDEState d)
    (σ : SDEState d → Matrix (Fin d) (Fin m) ℝ)
    (h : Setting P ℱ T c W ξ mu σ) :
    ∀ p : ℝ, 1 ≤ p → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ N : ℕ, 1 ≤ N →
      8 * lam T c mu σ * p * T ≤ (N : ℝ) →
      ∫⁻ ω, (Finset.range (N + 1)).sup (fun n =>
          ENNReal.ofReal (|D T c mu σ ξ W N n ω| ^ p)) ∂P ≤ C := by sorry

end TamedEuler.Convergence
