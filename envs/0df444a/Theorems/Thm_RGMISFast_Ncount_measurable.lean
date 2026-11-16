-- Prove2me | Theorems.Thm_RGMISFast_Ncount_measurable
-- name    : RGMISFast.Ncount_measurable
-- status  : Proved
-- author  : @srikkanthr
-- created : 2026-11-15T23:54:28.55543+00:00
-- url     : https://prove2.me/theorems/09f25b40-3eaa-485f-b57b-5e0ad4db0d6d
-- title:
--   Measurability of the active attached-extension count
-- statement:
--   For every finite graph, seed set $A$, extension size $k$, and real time $t$, the number $N_k(A;G_t)$ of attached $k$-sets whose union with $A$ is active at $t$ is a measurable function of the rank vector. This is the measurability clause required for the lower-integral formulation of Lemma 5.3. No rank-law or graph-degree assumptions are needed.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, §5.2, Lemma 5.3 and its proof, printed pp.20–21 (PDF pp.22–23). The short-window arrival derivative, contraction of A, Lemma 5.1, and Jensen inequality precede the final inverse-power integration.

import Mathlib
import Definitions.Def_RGMISFast_Y
import Definitions.Def_RGMISFast_condLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open RGMISFast

theorem RGMISFast.Ncount_measurable {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (k : ℕ) (t : ℝ) :
    Measurable (fun r : V → ℝ => Ncount G A k t r) := by sorry
