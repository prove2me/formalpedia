-- Prove2me | Theorems.Thm_StochGradTrack_Const_lemma_1
-- name    : StochGradTrack.Const.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:11.455259+00:00
-- url     : https://prove2.me/theorems/0f35aec7-0d70-4af9-8f96-315a299513ed
-- title:
--   Lemma 1, p. 415 — ρ_w < 1 and ‖Wω − 1ω̄‖ ≤ ρ_w‖ω − 1ω̄‖ for every ω ∈ ℝ^{n×p}
-- statement:
--   Let $\mathbf W\in\mathbb R^{n\times n}$ satisfy Assumptions 3 and 4: it is nonnegative and doubly stochastic, some diagonal entry is positive, $w_{ij}>0\iff w_{ji}>0$, and the graph on the agents with an edge $\{i,j\}$ ($i\ne j$) whenever $w_{ij}>0$ is connected. Let $\rho_w$ be the spectral norm of $\mathbf W-\frac1n\mathbf 1\mathbf 1^\top$. Then $\rho_w<1$, and for every $\omega\in\mathbb R^{n\times p}$, with $\bar\omega=\frac1n\mathbf 1^\top\omega$,
--   $$\|\mathbf W\omega-\mathbf 1\bar\omega\|\le\rho_w\|\omega-\mathbf 1\bar\omega\| ,$$
--   where $\|\cdot\|$ is the Frobenius norm.
--
--   The lemma is the contraction of one mixing step towards consensus; every consensus estimate of the paper, in particular (19) and (20), rests on it.
--
--   **Formalization Note.** Frobenius norms are written as $\big(\sum_i\|\cdot_i\|^2\big)^{1/2}$ over the rows. $\rho_w$ is the operator norm of $\mathbf W-\frac1n\mathbf 1\mathbf 1^\top$ on Euclidean $\mathbb R^n$. The paper cites [46] for the proof.
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), Lemma 1, p. 415

import Mathlib
import Definitions.Def_StochGradTrack_Const_Model

namespace StochGradTrack.Const

open MeasureTheory ProbabilityTheory Matrix

theorem lemma_1 {n p : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (hW : Assumption34 W) :
    rhoW W < 1 ∧
      ∀ ω : Stack n p,
        Real.sqrt (∑ i, ‖mix W ω i - avg ω‖ ^ 2) ≤ rhoW W * Real.sqrt (∑ i, ‖ω i - avg ω‖ ^ 2)
    := by sorry

end StochGradTrack.Const
