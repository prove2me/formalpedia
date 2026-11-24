-- Prove2me | Theorems.Thm_StableMSR_Recovery_SingleRAM_global_assembly_resource_bound
-- name    : StableMSR.Recovery.SingleRAM.global_assembly_resource_bound
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-23T22:25:16.133236+00:00
-- url     : https://prove2.me/theorems/fb31fbe4-a469-47c8-a3d2-0e3959dad85e
-- title:
--   Gate count, dense arena capacity, and formatting time of the exact regional assembly
-- statement:
--   For an $n$-point instance with $S$ input rows, let $G$ be the number of gates emitted by the stipulated ordered regional compiler after relocation and padding. We prove $G\le 2+SnA$, where $A=n^{75E(\varepsilon)}$. The three-record arena and the six-column final formatting pass consequently fit explicit bounds of $52\,\mathrm{cap}^4 A$ cells and $256\,\mathrm{cap}^3 A$ instructions respectively. The count also applies to empty and nonpositive-scale region slots.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_DenseGlobalAssembly
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 15000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleCodes
open StableMSR.Recovery.WindowProfiles (piece keys)
open StableMSR.Recovery.SingleWindows
open StableMSR.Recovery.SingleRAM

theorem StableMSR.Recovery.SingleRAM.global_assembly_resource_bound (x : World) (e : ℚ)
    (he : 0 < e) (hl : e < 1) (hn : 2 ≤ x.n) :
    let G := (globalAssembly x (budget (e:ℝ)) (widthBound (e:ℝ))).gates.size
    let A := x.n^(75*parameterEnvelope (e:ℝ))
    G ≤ 2+x.rows*x.n*A ∧
    2+5*(1+3*G*x.n*x.n) ≤ 52*x.cap^4*A ∧
    82+42*G+7*(G*x.n) ≤ 256*x.cap^3*A := by sorry
