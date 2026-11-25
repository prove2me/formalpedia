-- Prove2me | Theorems.Thm_PandoraKnapsack_Skipping_compiled_dyadic_sampler
-- name    : PandoraKnapsack.Skipping.compiled_dyadic_sampler
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T17:34:58.437601+00:00
-- url     : https://prove2.me/theorems/9262eed1-1540-5146-8448-08a068ee5f64
-- title:
--   A costed arithmetic program realizes the dyadic assignment sampler
-- statement:
--   There is one program on the mission’s coefficient-access pointer machine and one exponent $k$ such that, for every valid instance, the run budget
--   $$B=(n+m+\mathrm{bitlength}(T)+2)^k$$
--   suffices on every draw sequence. For each instance there is a repetition-free enumeration of the choice-time labels containing the support of the computed dyadic LP plan. The program halts within budget and its decoded list is exactly Algorithm 1 on that plan, with each item using its own uniform draw and the indicated enumeration for inverse sampling.
--
--   This is a pathwise implementation statement. It identifies the decoded policy before taking expectations, including at all endpoints of the sampling intervals.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen, Pandora’s Knapsack via Simple Policies, arXiv:2509.05956v5, https://arxiv.org/html/2509.05956v5#S5.SS1, Algorithm 1 and Theorem 5.1, Appendix B.1. Implementation lemma for the derived dyadic approximate solver on the exact machine in Prove2Me theorem 7898d376-37b2-42fd-8375-13696ef594ef.

import Definitions.Def_PandoraKnapsack_Skipping_DyadicPlan
import Definitions.Def_PandoraKnapsack_Skipping_UniformAssignment
import Definitions.Def_PandoraKnapsack_Skipping_Machine

open MeasureTheory

namespace PandoraKnapsack.Skipping

theorem compiled_dyadic_sampler :
    ∃ (P : Program) (k : ℕ), ∀ (n m T : ℕ) (I : Instance n m T), IsValid I →
      let B := (inputSize n m T + 2)^k
      ∃ (d : ℕ) (lab : Fin d → Fin m × Fin (T+1)) (hB : n ≤ B),
        Function.Injective lab ∧
        (∀ i j (t : Fin (T+1)), dyadicPlan I i j t.val ≠ 0 → ∃ u, lab u = (j,t)) ∧
        ∀ ω : Fin B → unitInterval,
          Halted P (run I (extendDraws ω) P B) ∧
          decodeOutput n m (run I (extendDraws ω) P B).core.mem =
            some (alg1Policy (uniformAssignment hB lab (dyadicPlan I) ω)) := by sorry

end PandoraKnapsack.Skipping
