-- Prove2me | Theorems.Thm_RossQC_Sufficient_eq_3
-- name    : RossQC.Sufficient.eq_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:31.813113+00:00
-- url     : https://prove2.me/theorems/19d69785-bda2-4b60-87ea-8a97bd26bb6e
-- title:
--   §3 equation (3) — the two-state Bellman equation
-- statement:
--   Let $0<\beta<1$, $0\le\pi\le1$, and $0<C<I<R$. For every bad-state belief $P\in[0,1]$, the finite-horizon values $V^n(P)$ defined by equation (4) converge to a bounded discounted value $V_\beta(P)$, and
--   $$
--   V_\beta(P)=\min\{CP+\beta V_\beta(T(P)),\ I+\beta P V_\beta(1)+\beta(1-P)V_\beta(\pi),\ R+\beta V_\beta(\pi)\},
--   $$
--   where $T(P)=P+\pi-\pi P$.
--
--   This equation characterizes the action costs used by all the remaining statements in this mission.
--
--   **Formalization Note** $V_\beta$ is the limit of value iteration starting at zero, rather than an arbitrary function assumed to solve the equation. Boundedness and pointwise convergence are explicit.
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, p. 590, §3, equations (3)–(4)

import Definitions.Def_RossQC_Sufficient_Model
open Filter

namespace RossQC.Sufficient

/-- Ross, *Quality Control under Markovian Deterioration*, §3, equation (3),
p. 590 (unnumbered claim around the displayed equation). The finite-horizon
values from (4) converge to a bounded `V_β` satisfying (3) on the belief
interval. -/
theorem eq_3 (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    (∀ P ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => M.valueIter n P) atTop (nhds (M.value P))) ∧
    (∃ B : ℝ, ∀ P ∈ Set.Icc (0 : ℝ) 1, |M.value P| ≤ B) ∧
    (∀ P ∈ Set.Icc (0 : ℝ) 1,
      M.value P = min (M.rhs3 M.value P .produce)
        (min (M.rhs3 M.value P .inspect) (M.rhs3 M.value P .revise))) := by sorry

end RossQC.Sufficient
