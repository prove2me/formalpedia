-- Prove2me | Theorems.Thm_RiskUncSets_Distortion_theorem_2_1
-- name    : RiskUncSets.Distortion.theorem_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:28:26.823165+00:00
-- url     : https://prove2.me/theorems/eba91090-818d-45ec-846d-bdcfa432f31a
-- title:
--   Theorem 2.1, p. 1485 — on a finite Ω, μ is coherent iff μ(X) = sup over a family of probability vectors of E_q[−X]
-- statement:
--   Let $\Omega = \{\omega_1, \dots, \omega_N\}$ with $N \ge 1$ carry a probability vector $p$ with $p_i > 0$ for every $i$. A function $\mu : \mathbb R^N \to \mathbb R$ is a coherent risk measure if and only if there is a family $\mathcal Q \subseteq \Delta^N$ of probability vectors, each absolutely continuous with respect to $p$, such that
--   $$\mu(X) = \sup_{q \in \mathcal Q} \mathbb E_q[-X] \qquad \text{for all } X \in \mathbb R^N. \tag{1}$$
--
--   This is the representation theorem of coherent risk measures: a coherent risk measure is the worst-case expected loss over a family of "generalized scenarios". The paper's endnote 3 observes that the general theorem requires the Fatou property, which holds automatically on a finite $\Omega$, so no such condition appears here. The family $\mathcal Q$ is arbitrary, not necessarily finite.
--
--   **Formalization Note** The family is an arbitrary `Set (Fin N → ℝ)` and (1) is `Generates Q μ` (an `IsLUB` statement, which also forces $\mathcal Q \neq \emptyset$). Absolute continuity $\mathbb Q \ll \mathbb P$ is the clause $p_i = 0 \Rightarrow q_i = 0$. Full support $p_i > 0$ is assumed and makes that clause vacuous: on a finite $\Omega$ with a null atom $\omega_0$, $\mu(X) = -X(\omega_0)$ is coherent on all functions but has no generating family $\ll \mathbb P$, whereas the paper works with random variables modulo null sets. $N \ge 1$ excludes the empty sample space, on which no function is a risk measure.
-- source:
--   Bertsimas & Brown, Constructing uncertainty sets for robust linear optimization, Oper. Res. 57(6) (2009), p. 1485, Theorem 2.1, display (1); endnote 3, p. 1494

import Mathlib
import Definitions.Def_RiskUncSets_Distortion_Setting

namespace RiskUncSets.Distortion

theorem theorem_2_1 {N : ℕ} (hN : 0 < N) (p : Fin N → ℝ) (hp : ∀ i, 0 < p i)
    (hp1 : ∑ i, p i = 1) (μ : (Fin N → ℝ) → ℝ) :
    IsCoherent μ ↔
      ∃ Q : Set (Fin N → ℝ), Generates Q μ ∧ ∀ q ∈ Q, ∀ i, p i = 0 → q i = 0 := by sorry

end RiskUncSets.Distortion
