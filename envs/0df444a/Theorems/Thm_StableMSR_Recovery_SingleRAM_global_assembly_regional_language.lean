-- Prove2me | Theorems.Thm_StableMSR_Recovery_SingleRAM_global_assembly_regional_language
-- name    : StableMSR.Recovery.SingleRAM.global_assembly_regional_language
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:24:40.430853+00:00
-- url     : https://prove2.me/theorems/c68e2110-33a3-4869-917b-2e92176128ed
-- title:
--   Global relocated circuit assembly realizes every regional root language
-- statement:
--   Assume that each live positive-scale call to `SingleCodes.regionalCircuit` has the exact ordered language specified by `LiveCircuitCorrect`. Then the global relocation and padding construction satisfies `RegionalLanguage`: missing slots generate only the empty word, nonpositive-scale live slots generate nothing, and positive-scale slots generate precisely the admissible owned window partitions without repetition. The flattened index is $r=un+i$, so positivity of $n$ identifies its quotient and remainder uniquely.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Global assembly step of the singleton dynamic-programming circuit construction.

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

theorem StableMSR.Recovery.SingleRAM.global_assembly_regional_language
    (x : World) (e : ℚ) (hn : 0 < x.n)
    (correct : ∀ u < x.rows, ∀ i < x.n, i ∈ keys x u → 0 < scale x u →
      LiveCircuitCorrect x (budget (e:ℝ)) (widthBound (e:ℝ)) u i) :
    let a := globalAssembly x (budget (e:ℝ)) (widthBound (e:ℝ))
    RegionalLanguage x e a.gates a.roots := by sorry
