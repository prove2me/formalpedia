-- Prove2me | Theorems.Thm_VWZClique_IntegerRAM_NativeArena_compiled_of_projection
-- name    : VWZClique.IntegerRAM.NativeArena.compiled_of_projection
-- status  : Proved
-- author  : @orz
-- created : 2026-11-20T14:07:31.820106+00:00
-- url     : https://prove2.me/theorems/adde9b56-d29b-49dc-86ca-6ef4c6ae7301
-- title:
--   Compiling the recursive weighted clique-counting program from its projected contraction
-- statement:
--   Assume the projected contraction satisfies the fixed word-RAM program and cost bounds in `ProjectionKernel`, with square multiplication charge $\mathrm{mm}$ and fixed parameter $T$. Then the weighted clique-counting recursion admits an implementation using that projection kernel, a fixed procedure for constructing its child instances, and a uniform word-width bound. The setup and per-child coefficients in the recursion cost model may both be taken to be $1$.
-- source:
--   V. Vassilevska Williams and O. Zamir, “The k-Clique hypothesis is dead, for good,” Theorem 1.1 and Appendix A. https://zamir.prof/kclq.pdf

import Mathlib
import Definitions.Def_VWZClique_NativeProjectionContract
import Definitions.Def_VWZClique_NativeCliqueCompiler

theorem VWZClique.IntegerRAM.NativeArena.compiled_of_projection
    {mm : ℕ → ℕ} {T : ℕ} (pk : VWZClique.IntegerRAM.NativeArena.ProjectionKernel mm T) :
    Nonempty (VWZClique.IntegerRAM.NativeFrame.Implemented mm T 1 1) := by sorry
