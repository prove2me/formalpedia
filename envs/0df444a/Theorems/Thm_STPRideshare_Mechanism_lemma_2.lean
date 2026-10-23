-- Prove2me | Theorems.Thm_STPRideshare_Mechanism_lemma_2
-- name    : STPRideshare.Mechanism.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:45.455388+00:00
-- url     : https://prove2.me/theorems/f774f4a6-8778-4e22-9f7c-f2b03d54be9f
-- title:
--   Lemma 2 (Integrality), p. 13 — the LP relaxation (9) has an integral optimal solution
-- statement:
--   Consider the linear program (9): over $x\in\mathbb R^{\mathcal R}$ and weights $y_{i,k}$ on the feasible paths $Z_{i,k}$ of each driver $i$,
--   $$\max\ \sum_{j\in\mathcal R}x_jv_j-\sum_{i\in\mathcal D}\sum_k y_{i,k}\lambda_{i,k}$$
--   subject to (10) $\sum_j x_j\mathbf 1\{(o_j,d_j,\tau_j)=(a,b,t)\}\le\sum_i\sum_k y_{i,k}\mathbf 1\{(a,b,t)\in Z_{i,k}\}$ for every trip $(a,b,t)\in\mathcal T$, (11) $\sum_k y_{i,k}=1$, (12)–(13) $0\le x_j\le 1$, and (14) $y_{i,k}\ge0$.
--
--   For every valid economy, this LP has an optimal solution $(x,y)$ in which every $x_j$ and every $y_{i,k}$ is $0$ or $1$.
--
--   Integrality makes the LP optimum equal to the best welfare $W(\mathcal D,\mathcal R)$ of an integral dispatching, which is what the dual arguments of Lemmas 3, 4 and 7 rely on.
--
--   **Formalization Note.** The weights $y_i$ are finitely supported functions on lists of trips, supported on the feasible paths of driver $i$; the list `[]` is the path $Z_{i,0}$.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 13, Lemma 2, LP (9)–(14) (proof pp. 37–40)

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_Model

namespace STPRideshare.Mechanism

/-- Lemma 2 (Integrality), p. 13: the LP relaxation (9) has an optimal solution `(x, y)` with
every `x_j` and every `y_{i,k}` in `{0, 1}`. -/
theorem lemma_2 {L ι κ : Type} [Fintype L] [Fintype ι] [Fintype κ] (e : Econ L ι κ)
    (he : e.Valid) :
    ∃ (x : κ → ℝ) (y : ι → List (Trip L) →₀ ℝ), e.LPFeasible x y ∧
      (∀ (x' : κ → ℝ) (y' : ι → List (Trip L) →₀ ℝ), e.LPFeasible x' y' →
        e.lpObj x' y' ≤ e.lpObj x y) ∧
      (∀ j, x j = 0 ∨ x j = 1) ∧ (∀ i k, y i k = 0 ∨ y i k = 1) := by sorry

end STPRideshare.Mechanism
