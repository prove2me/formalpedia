-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_BoundedSum_bounded_stream_writer
-- name    : StableMSR.Recovery.Compiler.BoundedSum.bounded_stream_writer
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-20T18:02:42.01996+00:00
-- url     : https://prove2.me/theorems/eb94b65e-374c-4fcf-8185-7c038bf8ba25
-- title:
--   Polynomial-time serialized integer output on the public RAM
-- statement:
--   Given bounded-sum descriptions of the output length and its entries, one deterministic program writes the complete stream at consecutive negative addresses and halts within a single uniform polynomial in the unary input size.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix B, Theorem B.2. Charged deterministic RAM implementation.

import Definitions.Def_StableMSR_BoundedSumRAM
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.BoundedSum
open Polynomial

theorem StableMSR.Recovery.Compiler.BoundedSum.bounded_stream_writer (len : ℕ→ℕ) (value : ℕ→ℕ→ℕ) (hl : Form (fun ρ=>len (ρ 0)))
    (hv : Form (fun ρ=>value (ρ 0) (ρ 1))) :
    ∃ a b : ℕ,0 < a ∧ 0 < b ∧ ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
    ∀m : ℕ,1 ≤ m → ∃t ≤ a*m^b,
      let s := execute P m 0 (fun _ _=>0) t
      s.halted=true ∧ s.work ≤ a*m^b ∧ len m ≤ a*m^b ∧
      ∀j < len m,s.imem (-1-(j:ℤ))=(value m j:ℤ) := by
  sorry
