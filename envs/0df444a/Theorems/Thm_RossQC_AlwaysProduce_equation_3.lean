-- Prove2me | Theorems.Thm_RossQC_AlwaysProduce_equation_3
-- name    : RossQC.AlwaysProduce.equation_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:07.894329+00:00
-- url     : https://prove2.me/theorems/43097963-acb4-4d7d-8ebf-8553f37ac9f6
-- title:
--   Equation (3) — the unique bounded two-state Bellman value
-- statement:
--   Let $0<\beta<1$, $0\le\pi\le1$, and $0<C<I<R$ in the two-state model. On the belief interval $[0,1]$, finite-horizon value iteration converges to a bounded value $V_\beta$. For every $P\in[0,1]$,
--
--   $$
--   V_\beta(P)=\min\{CP+\beta V_\beta(TP),\ I+\beta P V_\beta(1)+\beta(1-P)V_\beta(\pi),\ R+\beta V_\beta(\pi)\}.
--   $$
--
--   Any other bounded function on $[0,1]$ satisfying this equation there agrees with $V_\beta$ throughout the interval. This identifies the value against which the always-produce policy is compared.
--
--   **Formalization Note** The uniqueness clause is the two-state specialization of the assertion following equation (1) on p. 588. Boundedness and convergence are explicit because the Lean limit operator has a total value even on a divergent sequence.
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, p. 590, §3 equation (3); p. 588, §2 equation (1) and following uniqueness assertion

import Mathlib
import Definitions.Def_RossQC_AlwaysProduce_Model
open Filter

namespace RossQC.AlwaysProduce

/-- Ross, *Quality Control under Markovian Deterioration*, §3, equation (3),
p. 590, specialized from the uniqueness assertion following equation (1), p. 588.
Formalization Note: `value` is the limit of (4). Convergence and boundedness
are explicit, and uniqueness ranges over bounded functions on the state space
`[0,1]`. The good-state cost is zero, while `C` is the bad-state cost. -/
theorem equation_3 (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    (∀ P ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => M.valueIter n P) atTop (nhds (M.value P))) ∧
    (∃ B : ℝ, ∀ P ∈ Set.Icc (0 : ℝ) 1, |M.value P| ≤ B) ∧
    (∀ P ∈ Set.Icc (0 : ℝ) 1,
      M.value P = min (M.rhs3 M.value P .produce)
        (min (M.rhs3 M.value P .inspect) (M.rhs3 M.value P .revise))) ∧
    (∀ W : ℝ → ℝ,
      (∃ B : ℝ, ∀ P ∈ Set.Icc (0 : ℝ) 1, |W P| ≤ B) →
      (∀ P ∈ Set.Icc (0 : ℝ) 1,
        W P = min (M.rhs3 W P .produce)
          (min (M.rhs3 W P .inspect) (M.rhs3 W P .revise))) →
      ∀ P ∈ Set.Icc (0 : ℝ) 1, W P = M.value P) := by sorry

end RossQC.AlwaysProduce
