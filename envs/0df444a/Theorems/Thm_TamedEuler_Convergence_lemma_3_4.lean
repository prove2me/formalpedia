-- Prove2me | Theorems.Thm_TamedEuler_Convergence_lemma_3_4
-- name    : TamedEuler.Convergence.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:26.343425+00:00
-- url     : https://prove2.me/theorems/e772eb68-c9ac-4aea-89b3-59ab225ac357
-- title:
--   Lemma 3.4, p. 15 — uniform exponential moments of sup_n ± Σ_{k<n} α^N_k
-- statement:
--   In the standing setting of p. 2, let $\alpha^N_k$ be given by (25). Then
--   $$\sup_{z\in\{-1,1\}}\ \sup_{N\in\mathbb N}\ \mathbb E\Big[\sup_{n\in\{0,1,\dots,N\}}\exp\Big(pz\sum_{k=0}^{n-1}\alpha^N_k\Big)\Big]<\infty$$
--   for all $p\in[1,\infty)$.
--
--   It controls the martingale part of the exponent of the dominating processes $D^N_n$ (Lemma 3.5).
--
--   **Formalization Note** For each $p\ge1$ one finite constant bounds the expectation (a $[0,\infty]$-valued integral) for $z=\pm1$ and every $N\ge1$. The paper's preamble lists $\alpha^N_n$ for $n\le N$ while (25) defines it for $n\le N-1$; only $\alpha^N_0,\dots,\alpha^N_{N-1}$ enter the statement.
-- source:
--   Hutzenthaler, Jentzen, Kloeden, arXiv:1010.3756v2, p. 15, Lemma 3.4, (30)

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

/-- Hutzenthaler–Jentzen–Kloeden, arXiv:1010.3756v2, p. 15, Lemma 3.4, (30):
`sup_{z ∈ {−1,1}} sup_{N ∈ ℕ} 𝔼[sup_{n ∈ {0,…,N}} exp(pz Σ_{k=0}^{n−1} α^N_k)] < ∞` for all
`p ∈ [1, ∞)`, with `α^N_k` from (25). -/
theorem lemma_3_4 {d m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (c : ℝ)
    (W : ℝ≥0 → Ω → SDEState m) (ξ : Ω → SDEState d) (mu : SDEState d → SDEState d)
    (σ : SDEState d → Matrix (Fin d) (Fin m) ℝ)
    (h : Setting P ℱ T c W ξ mu σ) :
    ∀ p : ℝ, 1 ≤ p → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ z : ℝ, (z = -1 ∨ z = 1) → ∀ N : ℕ, 1 ≤ N →
      ∫⁻ ω, (Finset.range (N + 1)).sup (fun n => ENNReal.ofReal (Real.exp (p * z *
          ∑ k ∈ Finset.range n, alpha T mu σ ξ W N k ω))) ∂P ≤ C := by sorry

end TamedEuler.Convergence
