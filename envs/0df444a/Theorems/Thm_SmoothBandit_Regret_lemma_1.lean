-- Prove2me | Theorems.Thm_SmoothBandit_Regret_lemma_1
-- name    : SmoothBandit.Regret.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:33.07663+00:00
-- url     : https://prove2.me/theorems/76c5b8ea-e5d7-4dfd-a452-65f4dab50258
-- title:
--   Lemma 1, p. 11 — under Assumptions 2 and 3, ℙ(X ∈ 𝒬_a) ≥ p = µ_min c₀ r₀ᵈ v_d for a = ±1
-- statement:
--   Fix parameters in the standing range and an instance satisfying Assumption 2 (the optimal decision regions $\mathcal Q_{\pm1}$ are non-empty $(c_0, r_0)$-regular sets) and Assumption 3 (the context has a density between $\mu_{\min}$ and $\mu_{\max}$ on its compact support $\mathcal X \subseteq [0,1]^d$). Then each arm is optimal with probability bounded below by an explicit constant: for $a = \pm1$ and every round $t$,
--
--   $$P(X_t \in \mathcal Q_a) \ge p = \mu_{\min} c_0 r_0^d v_d ,$$
--
--   where $v_d$ is the volume of the unit ball of $\mathbb R^d$.
--
--   The constant $p$ enters the epoch lengths of the algorithm, and the lemma is what guarantees that each arm keeps receiving a constant fraction of the samples.
--
--   **Formalization Note.** The page writes $P(X \in \mathcal Q_a)$ for a generic context; the statement is given for every round $t$, all of which have the same law. The standing parameter range is assumed.
-- source:
--   Hu, Kallus & Mao, Smooth Contextual Bandits, arXiv:1909.02553v4, p. 11, Lemma 1 (proof p. 42)

import Mathlib
import Definitions.Def_SmoothBandit_Regret_Algorithm

open MeasureTheory

namespace SmoothBandit.Regret

theorem lemma_1 (d : ℕ) (hd : 1 ≤ d) (P : Params) (hP : P.Standing)
    (Ω : Type) [MeasurableSpace Ω] (M : Machine d Ω) (hM : IsMachine M)
    (h2 : Assumption2 P M) (h3 : Assumption3 P M) (a : Arm) (t : ℕ) :
    ENNReal.ofReal (pConst P d) ≤ M.P (M.X t ⁻¹' Q M a) := by sorry

end SmoothBandit.Regret
