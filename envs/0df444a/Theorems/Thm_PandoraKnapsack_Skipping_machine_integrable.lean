-- Prove2me | Theorems.Thm_PandoraKnapsack_Skipping_machine_integrable
-- name    : PandoraKnapsack.Skipping.machine_integrable
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T17:14:09.997669+00:00
-- url     : https://prove2.me/theorems/8549f74f-e5ce-49f8-8d04-f6b4f509c7f8
-- title:
--   Integrability of the payoff of a valid bounded-run randomized program
-- statement:
--   Fix an instance, a program of the costed real pointer machine, and a finite step budget $B$. Suppose each vector of uniform draws yields a valid decoded skipping policy (using the decoder's empty-list default). Its expected net utility as a function of the draws is integrable for their product uniform law:
--   $$
--   \omega\longmapsto V_I(\operatorname{output}(P,I,B,\omega))\ \in L^1.
--   $$
--
--   This supplies the integrability clause for bounded runs in Theorem 5.1.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen, Pandora's Knapsack via Simple Policies, arXiv:2509.05956v5, https://arxiv.org/html/2509.05956v5#S5.SS1, Theorem 5.1. Auxiliary consequence of the formalized real-RAM and bounded valid policy output in Prove2Me theorem 7898d376-37b2-42fd-8375-13696ef594ef.

import Definitions.Def_PandoraKnapsack_Skipping_Machine

open MeasureTheory

namespace PandoraKnapsack.Skipping

theorem machine_integrable {n m T : ℕ} (I : Instance n m T) (P : Program) (B : ℕ)
    (hv : ∀ ω : Fin B → unitInterval, IsSkippingPolicy T (outputPolicy I P B ω)) :
    Integrable (fun ω => skipValue I (outputPolicy I P B ω)) (drawLaw B) := by sorry

end PandoraKnapsack.Skipping
