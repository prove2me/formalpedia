-- Prove2me | Theorems.Thm_PandoraKnapsack_Skipping_uniformAssignment_law
-- name    : PandoraKnapsack.Skipping.uniformAssignment_law
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T17:30:35.553036+00:00
-- url     : https://prove2.me/theorems/271e1d63-3a2e-47ac-992b-8e3180dd72b1
-- title:
--   Uniform-draw sampling realizes the finite assignment law of Algorithm 1
-- statement:
--   Enumerate without repetition choice-time labels containing the support of a feasible time-indexed LP solution. Scan their categorical intervals using one independent uniform coordinate per item, with a draw budget $B\ge n$. The resulting policy utility is integrable and
--   $$\int V_I(\sigma(\omega))\,d\omega=U_I(x).$$
--   Thus a bounded-run uniform-draw implementation has exactly the assignment-averaged payoff of Algorithm 1.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen, Pandora’s Knapsack via Simple Policies, arXiv:2509.05956v5, https://arxiv.org/html/2509.05956v5#S5.SS1, Algorithm 1 and proof of Theorem 5.1. Sampling-law bridge for the formal costed machine.

import Definitions.Def_PandoraKnapsack_Skipping_UniformAssignment
import Definitions.Def_PandoraKnapsack_Skipping_Machine

open MeasureTheory

namespace PandoraKnapsack.Skipping

theorem uniformAssignment_law {n m T d B : ℕ} (I : Instance n m T) (x : LPArray n m) (hx : PsiFeasible I T x)
    (hB : n ≤ B) (lab : Fin d → Fin m × Fin (T+1)) (hinj : Function.Injective lab)
    (hsupp : ∀ (i : Fin n) (j : Fin m) (t : Fin (T+1)), x i j t.val ≠ 0 → ∃ k, lab k = (j,t)) :
    Integrable (fun ω => skipValue I (alg1Policy (uniformAssignment hB lab x ω))) (drawLaw B) ∧
    (∫ ω, skipValue I (alg1Policy (uniformAssignment hB lab x ω)) ∂drawLaw B) = alg1Utility I x := by sorry

end PandoraKnapsack.Skipping
