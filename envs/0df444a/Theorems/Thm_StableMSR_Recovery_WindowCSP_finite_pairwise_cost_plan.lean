-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowCSP_finite_pairwise_cost_plan
-- name    : StableMSR.Recovery.WindowCSP.finite_pairwise_cost_plan
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-21T16:10:14.036326+00:00
-- url     : https://prove2.me/theorems/67c073be-7454-418e-b55b-0b838aeaf408
-- title:
--   A bounded binary tree recurrence minimizes arbitrary unary real costs subject to pairwise constraints and exact counts
-- statement:
--   Enumerate only the products of local domains inside each bag. Assign each vertex and its additive count and real cost to one home bag. Check each ordered edge whose endpoints occur together in a bag. Tree decomposition coverage makes these checks equivalent to the original pairwise system, and the binary recurrence then realizes an optimum for every attainable exact count with explicit table and raw join bounds.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Lemmas 3.3, 3.8, 3.9(iii), 4.4, Proposition 4.2, Algorithm 1, and Appendix A.4–A.6. Alternative pairwise formulation using bounded-overlap window traces in the mission’s real-distance model.

import Definitions.Def_StableMSR_WindowPlans
import Definitions.Def_StableMSR_WindowCSP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.Supplement StableMSR.Recovery.RegionalSeeds StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000

theorem StableMSR.Recovery.WindowCSP.finite_pairwise_cost_plan {V X : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (w : ℕ)
    (tw : RobertsonSeymour1986.GM5.TreewidthLE G w) (D : V→Finset X) (fallback : X)
    (test : V→V→X→X→Prop) (cnt : V→X→ℕ) (cost' : V→X→ℝ) (B : ℕ)
    (bpos : 1≤ B) (bd : ∀v,(D v).card≤ B) :
    ∃p : TreeDP.Plan V X,p.Coherent ∧ p.Local ∧ p.nodes≤2*Fintype.card V+1 ∧
    p.AllData (fun d=>d.bag.card≤ w+1 ∧ d.choices.card≤ B^(w+1)) ∧
    (∀cap,p.tableVolume cap≤(2*Fintype.card V+1)*(B^(w+1)*(cap+1)) ∧
      p.rawCandidateVolume cap≤(2*Fintype.card V+1)*((B^(w+1))^3*(cap+1)^2)) ∧
    ∀cap j,j≤ cap → ∀f : V→X,admissible G D test f → (∑v,cnt v (f v))=j →
      ∃u∈TreeDP.solve cap p,∃g : V→X,u.2.1=j ∧ admissible G D test g ∧
        (∑v,cnt v (g v))=j ∧ (∑v,cost' v (g v))=u.2.2 ∧
        ∀g' : V→X,admissible G D test g' → (∑v,cnt v (g' v))=j → u.2.2≤∑v,cost' v (g' v) := by
  sorry
