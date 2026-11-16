-- Prove2me | Theorems.Thm_PolyhedralPacking1261_Packing_Supplement_theorem_2
-- name    : PolyhedralPacking1261.Packing.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:39:00.014204+00:00
-- url     : https://prove2.me/theorems/3a604556-b959-4b5c-a89d-4b36efee98ba
-- title:
--   Theorem 2 — one polynomial-time algorithm with ratio $O(\log^{69} n)$, and $O(\log^7 n)$ under the Kakeya maximal estimate
-- statement:
--   There is a single polynomial-time algorithm for translational packing of convex polyhedra in $\mathbb R^3$ into a minimum-volume axis-parallel box with the following two guarantees. Write $n\ge1$ for the number of input polyhedra and $\mathrm{OPT}_{\mathrm{vol}}$ for the optimal container volume.
--
--   1. Unconditionally (using OpenAI's formally verified tube estimate), there is an absolute constant $C>0$ such that on every input the returned packing is feasible and its box has volume
--   $$\mathrm{vol}\le C\,(1+\ln n)^{69}\,\mathrm{OPT}_{\mathrm{vol}}.$$
--   2. If the Kakeya maximal estimate (Theorem 18, claimed in OpenAI's preprint, Corollary 9.1) holds, then the same algorithm satisfies, for some absolute constant $C'>0$,
--   $$\mathrm{vol}\le C'\,(1+\ln n)^{7}\,\mathrm{OPT}_{\mathrm{vol}}.$$
--
--   The algorithm, its polynomial running-time bound and the attainment of the optimum are as in Theorem 1; since $(1+\ln n)^{69}\le C_\varepsilon n^\varepsilon$ for each $\varepsilon>0$, the first guarantee contains the $n^{o(1)}$ ratio of Theorem 1. This is the paper's polylogarithmic sharpening of its headline result.
--
--   **Formalization Note** The algorithm is a finite program of the base mission's exact-real scalar machine, chosen before both clauses; $O(\log^q n)$ is written with $1+\ln n$ so that the case $n=1$ is a genuine constant-factor bound.
--
--   Differences from the source:
--   - reading: the algorithm of Theorem 1 achieves …; … the ratio improves to … → there is one finite scalar program, with one polynomial time bound, feasible on every admissible input, satisfying both the unconditional and the conditional rate; reason: the paper identifies its algorithm only by its prose description (Algorithm 2); the Lean asserts one program carrying both rates, and the log⁶⁹ rate implies the n^ε rate of Theorem 1, so the program is an algorithm of Theorem 1; a scalar-code transcription of Algorithm 2 (including the Li–Cheng strip packer) was not written, see STATUS.md
--   - reading: approximation ratio O(log^69 n), O(log^7 n) → ∃ C > 0, fixed before every input, with containerVolume ≤ C·(1 + ln n)^q·OPT_vol (q = 69, 7); reason: uniform reading of O over all inputs and sizes; 1 + ln n equals ln n up to constants for n ≥ 2 and keeps n = 1 meaningful
--   - reading: If the Kakeya maximal estimate claimed by OpenAI [38, Corollary 9.1] holds → KakeyaMaximalEstimate (Theorem 18 as stated in Appendix B.1) as hypothesis of the second clause only; reason: the paper quotes [38, Corollary 9.1] as Theorem 18; the unconditional clause carries no such hypothesis
--   - encoding: algorithms on n convex polyhedra in ℝ³, polynomial time, translational packing into an axis-parallel box → the base mission's published model: finite exact-real scalar programs on the full vertex encoding, time counted to the first halt, all affine dimensions allowed, ambient interiors disjoint with boundary contact; reason: the published conventions of the mission this supplement extends; no instance of the source problem is excluded
-- source:
--   Simon Bartlmae, Anders Aamand, Mikkel Abrahamsen, Polylogarithmic Approximation for Packing Convex Polyhedra, STOC 2027 submission #1261 (October 2026), canonical PDF SHA-256 b915da2d5fece730ea9946885b05ad09e10e575374e6a1df96e8a6149cb0e67e, Theorem 2, PDF p.3 (printed p.2); proof in Appendix B.2, PDF p.28 (printed p.27)

import Definitions.Def_PolyhedralPacking1261_Packing_Execution
import Definitions.Def_PolyhedralPacking1261_Packing_Supplement_Kakeya

set_option autoImplicit false

namespace PolyhedralPacking1261.Packing.Supplement

open PolyhedralPacking1261.Packing

/-- Theorem 2, PDF p.3 (printed p.2). One finite scalar program with one polynomial
running-time bound returns feasible translational packings of every admissible input,
with ratio `O(log^69 n)` unconditionally and, if the Kakeya maximal estimate
(Theorem 18) holds, ratio `O(log^7 n)` for the same program. `O(log^q n)` is read
uniformly as `C (1 + ln n)^q` with `C` fixed before every input, `n ≥ 1`. -/
theorem theorem_2 :
    ∃ program : ScalarProgram, ∃ coefficient degree : ℕ, 0 < coefficient ∧
      (∀ K : PackingInput, AdmissibleInput K →
        HasAttainedOptimum K ∧
        ∃ time out, PackingExecution program K time out ∧
          time ≤ coefficient * (packingInputSize K + 1) ^ degree ∧
          FeasiblePacking K out) ∧
      (∃ C : ℝ, 0 < C ∧
        ∀ K : PackingInput, AdmissibleInput K →
          ∀ time out, PackingExecution program K time out →
            FeasiblePacking K out ∧
            containerVolume out ≤
              C * (1 + Real.log (K.length : ℝ)) ^ 69 * optimumVolume K) ∧
      (KakeyaMaximalEstimate → ∃ C : ℝ, 0 < C ∧
        ∀ K : PackingInput, AdmissibleInput K →
          ∀ time out, PackingExecution program K time out →
            FeasiblePacking K out ∧
            containerVolume out ≤
              C * (1 + Real.log (K.length : ℝ)) ^ 7 * optimumVolume K) := by sorry

end PolyhedralPacking1261.Packing.Supplement
