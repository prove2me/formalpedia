-- Prove2me | Theorems.Thm_TamedEuler_Convergence_lemma_3_9
-- name    : TamedEuler.Convergence.lemma_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:43.261826+00:00
-- url     : https://prove2.me/theorems/b137ee93-d256-4abb-801b-40e6a2b3c766
-- title:
--   Lemma 3.9, p. 16 — uniformly bounded moments of the tamed Euler approximations: sup_N sup_n 𝔼‖Y^N_n‖^p < ∞
-- statement:
--   In the standing setting of p. 2, let $Y^N_n$ be the tamed Euler approximations (8). Then
--   $$\sup_{N\in\mathbb N}\ \sup_{n\in\{0,1,\dots,N\}}\mathbb E\big[\|Y^N_n\|^p\big]<\infty$$
--   for all $p\in[1,\infty)$.
--
--   These a priori moment bounds, (12) of the introduction, are the key difficulty of the paper: they fail for the explicit Euler scheme when the drift grows superlinearly, and once they hold the convergence proof follows the globally Lipschitz pattern.
--
--   **Formalization Note** For each $p\ge1$ one finite constant bounds the $[0,\infty]$-valued expectation for every $N\ge1$ and every $n\le N$.
-- source:
--   Hutzenthaler, Jentzen, Kloeden, arXiv:1010.3756v2, p. 16, Lemma 3.9, (35); cf. (12), p. 6

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_TamedEuler_Convergence_Setting
import Definitions.Def_TamedEuler_Convergence_Scheme

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace TamedEuler.Convergence

open EthierKurtz

/-- Hutzenthaler–Jentzen–Kloeden, arXiv:1010.3756v2, p. 16, Lemma 3.9 (Uniformly bounded
moments of the tamed Euler approximations), (35):
`sup_{N ∈ ℕ} sup_{n ∈ {0,…,N}} 𝔼[‖Y^N_n‖^p] < ∞` for all `p ∈ [1, ∞)`. -/
theorem lemma_3_9 {d m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (c : ℝ)
    (W : ℝ≥0 → Ω → SDEState m) (ξ : Ω → SDEState d) (mu : SDEState d → SDEState d)
    (σ : SDEState d → Matrix (Fin d) (Fin m) ℝ)
    (h : Setting P ℱ T c W ξ mu σ) :
    ∀ p : ℝ, 1 ≤ p → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ N : ℕ, 1 ≤ N → ∀ n : ℕ, n ≤ N →
      ∫⁻ ω, ENNReal.ofReal (‖Y T mu σ ξ W N n ω‖ ^ p) ∂P ≤ C := by sorry

end TamedEuler.Convergence
