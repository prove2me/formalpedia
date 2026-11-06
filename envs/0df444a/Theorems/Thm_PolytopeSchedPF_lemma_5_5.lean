-- Prove2me | Theorems.Thm_PolytopeSchedPF_lemma_5_5
-- name    : PolytopeSchedPF.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:20:33.502264+00:00
-- url     : https://prove2.me/theorems/96c98df0-1deb-4e38-bca2-aeeefdf862d4
-- title:
--   Lemma 5.5 — the $\alpha$-greedy schedule is feasible and $\mathrm{OPT}(p)\le\mathrm{GR}_\alpha(p)\le\langle\alpha,p\rangle$
-- statement:
--   Let $w>0$ and $\alpha\in\mathbb R^n_{\ge0}$ with $H_\alpha(U)\ge w(U)$ for all $U\subseteq J$, and fix for every $U$ a rate vector $y^U\in\mathcal P_U$ with $\langle\alpha,y^U\rangle=H_\alpha(U)$. Then for every $p\in\mathbb R^n_{\ge0}$ (release dates $0$) an $\alpha$-greedy schedule for $p$ exists, and every $\alpha$-greedy schedule is feasible with weighted completion time $\mathrm{GR}_\alpha(p)$ satisfying
--   $$
--   \mathrm{OPT}(p)\le\mathrm{GR}_\alpha(p)\le\langle\alpha,p\rangle .
--   $$
--   This is the upper half of Theorem 5.6.
--
--   Differences from the source:
--   - reading: "the α-greedy schedule for p is feasible" for a fixed family y^U → for every family y^U of maximizers: a greedy schedule exists, and every greedy schedule is feasible with the two bounds; reason: the paper fixes an arbitrary family and speaks of the schedule it induces; the statement covers every family and every schedule following the rule
--   - encoding: OPT(p), GR_α(p) → opt0 P w p and the weighted completion time of the greedy schedule; reason: release dates 0 as in §5
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, Lemma 5.5, p.28 (PDF p.30), with the α-greedy schedule of p.27

import Mathlib
import Definitions.Def_PolytopeSchedPF_Orders

namespace PolytopeSchedPF

/-- **Lemma 5.5** (α-greedy schedule; Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, §5.2, p.28). Let `α ∈ ℝⁿ_{≥0}` such that
`H_α(U) ≥ w(U)` for all `U ⊆ J`. Then, for every `p ∈ ℝⁿ_{≥0}`, the α-greedy schedule for `p`
is feasible, and `OPT(p) ≤ GR_α(p) ≤ ⟨α, p⟩`.

**Formalization Note** Release dates are `0` (§5). Reading R12: the statement holds for every
family `y^U ∈ P_U` with `⟨α, y^U⟩ = H_α(U)` (p.27); "the α-greedy schedule" becomes "an α-greedy
schedule exists, and every α-greedy schedule is feasible", and `GR_α(p)` is its weighted
completion time. -/
theorem lemma_5_5 {n D : ℕ} (P : RatePolytope n D) (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (α : Fin n → ℝ) (hα : ∀ j, 0 ≤ α j) (hH : ∀ U : Finset (Fin n), wsum w U ≤ P.H α U)
    (yU : Finset (Fin n) → Fin n → ℝ)
    (hyU : ∀ U, yU U ∈ P.restricted U ∧ dot α (yU U) = P.H α U)
    (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) :
    (∃ y, IsGreedySchedule p yU y) ∧
    ∀ y, IsGreedySchedule p yU y →
      IsFeasible P p 0 y ∧ opt0 P w p ≤ weightedCompletion w p 0 y ∧
        weightedCompletion w p 0 y ≤ dot α p := by sorry

end PolytopeSchedPF
