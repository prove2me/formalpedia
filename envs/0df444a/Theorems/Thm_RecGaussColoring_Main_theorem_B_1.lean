-- Prove2me | Theorems.Thm_RecGaussColoring_Main_theorem_B_1
-- name    : RecGaussColoring.Main.theorem_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:35.639396+00:00
-- url     : https://prove2.me/theorems/5979512d-374a-4f85-866a-f184fd6768d2
-- title:
--   Theorem B.1 — dense progress
-- statement:
--   There exist an exponent function $g:\mathbb N\to\mathbb R$ with $g(n)\to0$, a constant $C>0$, and one deterministic polynomial-time algorithm such that every three-colorable $n$-vertex graph of minimum degree $d>\sqrt n$ yields a Blum progress output toward
--   $$
--   f(n,d)=n^{g(n)}\sqrt{n/d}.
--   $$
--   The output is one of P1, P2 or P3, with the same constant $C$ for all graphs. This is the dense progress result cited from KTY24, Theorem 1.
--
--   Differences from the source:
--   - encoding: n^{o(1)}√(n/d) and O/Ω progress constants → one sequence g(n)→0 and a positive C, fixed before all graph inputs; reason: this makes both forms of uniformity explicit
--   - reading: in polynomial time → deterministic DetSolves on the shared bounded-bit integer RAM; reason: this is the stronger deterministic reading required by Appendix B; the cited KTY24 proof is not supplied in this source
-- source:
--   Ijay Narang, Yukai Tang, STOC 2027 submission #295 (October 2026), Theorem B.1, p. 26. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/295.pdf

import Definitions.Def_RecGaussColoring_Main_Progress

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
noncomputable section

namespace RecGaussColoring.Main

/-- Theorem B.1, p. 26, with one subpolynomial exponent sequence and deterministic program. -/
theorem theorem_B_1 :
  ∃ g : ℕ → ℝ, Tendsto g atTop (𝓝 0) ∧ ∃ C : ℝ, 0 < C ∧
    CongruencyTU.DetSolves encGraph graphSize
      (fun I => ThreeColorable I ∧ Real.sqrt (I.n : ℝ) < (minDeg I : ℝ))
      (fun I out => IsProgress C
        ((I.n : ℝ)^(g I.n) * Real.sqrt ((I.n : ℝ)/(minDeg I : ℝ))) I out) := by sorry

end RecGaussColoring.Main
