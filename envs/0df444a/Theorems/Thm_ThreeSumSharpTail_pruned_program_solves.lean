-- Prove2me | Theorems.Thm_ThreeSumSharpTail_pruned_program_solves
-- name    : ThreeSumSharpTail.pruned_program_solves
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T20:56:38.10844+00:00
-- url     : https://prove2.me/theorems/8777def1-6656-496d-a34f-e968a7f53458
-- title:
--   Polynomial native resources for the arbitrary-parameter pruned program
-- statement:
--   For every rational parameter record G there is a polynomial native Need which, under CostsWithinP and the native Lop-count task precondition, guarantees the actual offline32 Meets specification of program31P G. The conclusion holds for every appended program, free pointer and sufficiently large word, space and depth limits. The runtime is the original natural tOffline32P step count.
-- source:
--   Generic resource and execution assembly from the accepted pruned program source. Uses actual Hyp30 below/top bounds and the proved generic program correctness interface; no fixed numerical parameter specialization is assumed.

import Definitions.Def_APSP299791_Defs5

theorem ThreeSumSharpTail.pruned_program_solves (G : Light.Sec4.RatParams) :
    ∃ need : List ℕ → Light.Need, Light.PolyNeedN need ∧
      ∀ (R : Light.Program) (lim : Light.Limits) (fr d : ℕ)
        (x : Light.ThinInst) (μ : ℕ → ℤ) (C tp tq : ℝ),
        0 ≤ C → Light.lopCountTask.Pre x μ fr →
        Light.Sec4.CostsWithinP G C x.N x.D tp tq →
        (need [x.N, x.D, x.w, x.U]).Ok lim fr d →
        Light.Meets lim (Light.Sec4.program31P G ++ R) Light.Sec4.Proc.offline32 (d + 1)
          [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ
          (Light.Sec4.tOffline32P Light.Sec4.cShared30 G x.N x.D x.w)
          (fun r μ' => Light.lopCountTask.Post x μ fr r μ') := by sorry
