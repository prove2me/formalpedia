-- Prove2me | Theorems.Thm_QMaxCutBeyond_TwoQubit_weighted_eq_15
-- name    : QMaxCutBeyond.TwoQubit.weighted_eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:12.65383+00:00
-- url     : https://prove2.me/theorems/d46d65a7-f696-43ef-aeb1-a6d00be70b90
-- title:
--   Weighted form of Eq. (15) — OPT(G) ≤ W + ½ Σ_v max_{e∼v} w_e
-- statement:
--   Let $G=(V,E,w)$ be a graph with nonnegative weights and $W=\sum_{e\in E}w_e$. Then
--   $$\mathrm{OPT}(G)=\|H_G\|\;\le\;W+\frac12\sum_{v\in V}\max_{e\sim v}w_e ,$$
--   where $\max_{e\sim v}w_e$ is the largest weight of an edge incident to $v$ ($0$ if $v$ is isolated).
--
--   This is the weighted replacement of eq. (15) in the proof of Theorem 3; it is the upper bound on the optimum against which all candidate states are compared.
--
--   **Formalization Note** Stated as: every unit state has energy at most the right-hand side. The paper derives it by "exactly the same arguments" as eqs. (14)–(15), written there for unit weights; this item is that weighted form.
-- source:
--   Anshu, Gosset & Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394v1, proof of Theorem 3, p. 9 (weighted Eq. (15)); W defined on p. 10

import Mathlib
import Definitions.Def_QMaxCutBeyond_TwoQubit_Setting

namespace QMaxCutBeyond.TwoQubit

/-- Weighted form of Eq. (15), proof of Theorem 3, p. 9:
`OPT(G) ≤ W + ½ Σ_{v∈V} max_{e∼v} w_e`, stated for every unit state. -/
theorem weighted_eq_15 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : ∀ e, 0 ≤ w e)
    (ψ : Config n → ℂ) (hψ : IsUnitState ψ) :
    energy (hamiltonian G w) ψ ≤ totalWeight G w + (1 / 2) * ∑ v, maxIncident G w v := by sorry

end QMaxCutBeyond.TwoQubit
