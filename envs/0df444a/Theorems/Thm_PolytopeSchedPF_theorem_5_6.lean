-- Prove2me | Theorems.Thm_PolytopeSchedPF_theorem_5_6
-- name    : PolytopeSchedPF.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:20:51.747432+00:00
-- url     : https://prove2.me/theorems/1a7b89f1-87c7-4161-a370-28c3159327eb
-- title:
--   Theorem 5.6 — $\mathrm{OPT}(p)=\min_\pi\langle\alpha^\pi,p\rangle$, optimal greedy schedules, and concavity of $\mathrm{OPT}$
-- statement:
--   Consider a support-submodular PSP instance with weights $w>0$, and for every order $\pi$ let $\alpha^\pi\in\mathbb R^n_{\ge0}$ be the price vector for which every suffix of $\pi$ is tight (Lemma 5.1). Let $p\in\mathbb R^n_{\ge0}$, all jobs released at time $0$. Then
--
--   1. $\displaystyle\mathrm{OPT}(p)=\min_{\pi\in S_n}\langle\alpha^\pi,p\rangle$; (15)
--   2. for every order $\pi$ attaining this minimum, the $\alpha^\pi$-greedy schedule for $p$ (for any family of maximizers $y^U$) exists and is optimal, so an optimal schedule for $p$ exists;
--   3. conversely, every order in which some optimal schedule for $p$ completes the jobs attains this minimum.
--
--   In particular, the optimal-value function $p\mapsto\mathrm{OPT}(p)$ is concave on $\mathbb R^n_{\ge0}$.
--
--   Concavity of $\mathrm{OPT}$ is what the proof of Theorem 1.3 uses, through Jensen's inequality over time.
--
--   Differences from the source:
--   - encoding: α^π, the vector of Lemma 5.1 → a family α : Perm (Fin n) → ℝⁿ with α π ≥ 0 and every suffix of π tight for α π; reason: unique by Lemma 5.1; avoids a choice function
--   - reading: "the α^π-greedy schedule for p is optimal" → for every family y^U of maximizers of ⟨α^π, ·⟩ over P_U, a greedy schedule exists and every greedy schedule is feasible with weighted completion time OPT(p); reason: the paper fixes an arbitrary family (p.27); this covers every family
--   - encoding: min over π ∈ S_n → an order attaining the value together with the bound for every order; reason: a minimum over a finite nonempty set
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, Theorem 5.6, p.28 (PDF p.30), display (15)

import Mathlib
import Definitions.Def_PolytopeSchedPF_Orders
import Definitions.Def_PolytopeSchedPF_IsSupportSubmodular

namespace PolytopeSchedPF

/-- **Theorem 5.6** (Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, §5.2, p.28). Consider a support-submodular PSP instance, and let
`p ∈ ℝⁿ_{≥0}`. Then `OPT(p) = min_{π∈S_n} ⟨α^π, p⟩` (15). For every order `π` attaining this
minimum, the `α^π`-greedy schedule for `p` is optimal, so an optimal schedule for `p` exists.
Conversely, every order in which some optimal schedule for `p` completes the jobs attains this
minimum. In particular, the optimal-value function `p ↦ OPT(p)` is concave on `ℝⁿ_{≥0}`.

**Formalization Note** Release dates are `0` (§5); `OPT` is `opt0`. The prices `α^π` are given as
a family `α` with every suffix of `π` tight for `α π` (unique by Lemma 5.1), so no choice
function is involved. Greedy schedules follow reading R12: every family `y^U` of maximizers of
`⟨α^π, ·⟩` over `P_U` and every greedy schedule for it. "Optimal" means feasible with weighted
completion time `OPT(p)`. -/
theorem theorem_5_6 {n D : ℕ} (P : RatePolytope n D) (hP : IsSupportSubmodular P)
    (w : Fin n → ℝ) (hw : ∀ j, 0 < w j) (α : Equiv.Perm (Fin n) → Fin n → ℝ)
    (hα : ∀ π j, 0 ≤ α π j)
    (htight : ∀ π, ∀ b : ℕ, b ≤ n → P.H (α π) (suffix π b) = wsum w (suffix π b)) :
    (∀ p : Fin n → ℝ, (∀ j, 0 ≤ p j) →
      ((∃ π, opt0 P w p = dot (α π) p) ∧ ∀ π, opt0 P w p ≤ dot (α π) p) ∧
      (∀ π, (∀ π', dot (α π) p ≤ dot (α π') p) →
        ∀ yU : Finset (Fin n) → Fin n → ℝ,
          (∀ U, yU U ∈ P.restricted U ∧ dot (α π) (yU U) = P.H (α π) U) →
          (∃ y, IsGreedySchedule p yU y) ∧
          ∀ y, IsGreedySchedule p yU y →
            IsFeasible P p 0 y ∧ weightedCompletion w p 0 y = opt0 P w p) ∧
      (∃ y, IsFeasible P p 0 y ∧ weightedCompletion w p 0 y = opt0 P w p) ∧
      (∀ y, IsFeasible P p 0 y → weightedCompletion w p 0 y = opt0 P w p →
        ∀ π, CompletesInOrder p 0 y π → ∀ π', dot (α π) p ≤ dot (α π') p)) ∧
    ConcaveOn ℝ {p : Fin n → ℝ | ∀ j, 0 ≤ p j} (opt0 P w) := by sorry

end PolytopeSchedPF
