-- Prove2me | Theorems.Thm_PolyhedralPacking1261_Packing_Supplement_theorem_3
-- name    : PolyhedralPacking1261.Packing.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:40:44.672193+00:00
-- url     : https://prove2.me/theorems/94c7d437-e94a-4e35-a4c4-ce374a0a4c8c
-- title:
--   Theorem 3 — an $\alpha$-approximation for volume gives $O(\alpha/\delta^3)$ bin and $O(\alpha/\delta^2)$ strip approximations
-- statement:
--   Suppose translational packing of convex polyhedra in $\mathbb R^3$ into a minimum-volume axis-parallel box admits a polynomial-time $\alpha$-approximation. Then for every $0<\delta<1$, translational bin packing and strip packing of convex polyhedra with all coordinate widths at most $1-\delta$ admit polynomial-time $O(\alpha/\delta^3)$- and $O(\alpha/\delta^2)$-approximation algorithms, respectively.
--
--   Precisely: there are absolute constants $C_{\mathrm{bin}},C_{\mathrm{strip}}>0$ such that for every factor $\alpha(n)\ge1$, every polynomial-time algorithm returning on each input of $n$ polyhedra a feasible box packing of volume at most $\alpha(n)\,\mathrm{OPT}_{\mathrm{vol}}$, and every $0<\delta<1$, there are polynomial-time algorithms that on every input with coordinate widths at most $1-\delta$ return
--
--   1. a feasible packing into at most $C_{\mathrm{bin}}\,\alpha(n)\,\delta^{-3}\,\mathrm{OPT}_{\mathrm{bin}}$ unit cubes, and
--   2. a feasible packing into $[0,1]^2\times[0,H]$ with $H\le C_{\mathrm{strip}}\,\alpha(n)\,\delta^{-2}\,\mathrm{OPT}_{\mathrm{strip}}$.
--
--   With Theorem 1 one may take $\alpha=n^{o(1)}$ and with Theorem 2 $\alpha=O(\log^{69}n)$.
--
--   **Formalization Note** All algorithms are finite programs of the base mission's scalar machine; the bin and strip programs and their running-time bounds may depend on $\delta$ and on the given volume program, while the two constants do not.
--
--   Differences from the source:
--   - reading: a polynomial-time α-approximation → a finite scalar program with a polynomial time bound on all admissible inputs whose every output is feasible with volume ≤ α(n)·OPT_vol, for an arbitrary α : ℕ → ℝ with α(n) ≥ 1; reason: the paper applies the theorem with α = n^{o(1)}, so α may depend on n; a constant α is the special case of a constant function
--   - reading: O(α/δ³)- and O(α/δ²)-approximation → absolute constants C_bin, C_strip > 0 fixed before α, the volume program, δ and the input, with count ≤ C_bin·α(n)/δ³·OPT_bin and height ≤ C_strip·α(n)/δ²·OPT_strip; reason: uniform reading of O with δ and α explicit; the proof gives 81 and 80
--   - reading: for every 0 < δ < 1 … admit polynomial-time algorithms → for each δ ∈ (0,1) there exist bin and strip programs with their own polynomial bounds; reason: the algorithms are quantified after δ in the source
--   - encoding: bin packing into unit cubes; strip [0,1]²×[0,h] of minimum height; coordinate widths at most 1 − δ → BinFeasible/optimumBins (least feasible ℕ count), StripFeasible/optimumHeight (infimum of feasible heights), WidthsAtMost (1 − δ) on vertex coordinates; reason: the source's objectives; the width of a convex hull in a coordinate is the largest vertex difference
--   - encoding: algorithms on n convex polyhedra in ℝ³, polynomial time, translational packing into an axis-parallel box → the base mission's published model: finite exact-real scalar programs on the full vertex encoding, time counted to the first halt, all affine dimensions allowed, ambient interiors disjoint with boundary contact; reason: the published conventions of the mission this supplement extends; no instance of the source problem is excluded
-- source:
--   Simon Bartlmae, Anders Aamand, Mikkel Abrahamsen, Polylogarithmic Approximation for Packing Convex Polyhedra, STOC 2027 submission #1261 (October 2026), canonical PDF SHA-256 b915da2d5fece730ea9946885b05ad09e10e575374e6a1df96e8a6149cb0e67e, Theorem 3, PDF p.3 (printed p.2); proof in §5, PDF p.21 (printed p.20)

import Definitions.Def_PolyhedralPacking1261_Packing_Supplement_Containers

set_option autoImplicit false

namespace PolyhedralPacking1261.Packing.Supplement

open PolyhedralPacking1261.Packing

/-- Theorem 3, PDF p.3 (printed p.2). Absolute constants `C_bin, C_strip > 0` are fixed
first. For every approximation factor `α(n) ≥ 1` and every finite scalar program that
runs in polynomial time and is an `α`-approximation for minimum-volume translational
packing on all admissible inputs, and for every `0 < δ < 1`, there are polynomial-time
finite scalar programs for translational bin packing and strip packing whose outputs,
on every admissible input with all coordinate widths at most `1 - δ`, are feasible and
within `C_bin α(n) / δ³ · OPT_bin` bins and height `C_strip α(n) / δ² · OPT_strip`. -/
theorem theorem_3 :
    ∃ Cbin Cstrip : ℝ, 0 < Cbin ∧ 0 < Cstrip ∧
      ∀ α : ℕ → ℝ, (∀ n, 1 ≤ α n) →
      ∀ (volumeProgram : ScalarProgram) (coefficient degree : ℕ),
        (∀ K : PackingInput, AdmissibleInput K →
          (∃ time out, PackingExecution volumeProgram K time out ∧
            time ≤ coefficient * (packingInputSize K + 1) ^ degree) ∧
          ∀ time out, PackingExecution volumeProgram K time out →
            FeasiblePacking K out ∧
            containerVolume out ≤ α K.length * optimumVolume K) →
      ∀ δ : ℝ, 0 < δ → δ < 1 →
        (∃ binProgram : ScalarProgram, ∃ c d : ℕ, 0 < c ∧
          ∀ K : PackingInput, AdmissibleInput K → WidthsAtMost (1 - δ) K →
            (∃ time out, BinExecution binProgram K time out ∧
              time ≤ c * (packingInputSize K + 1) ^ d) ∧
            ∀ time out, BinExecution binProgram K time out →
              BinFeasible K out ∧
              (out.count : ℝ) ≤ Cbin * α K.length / δ ^ 3 * (optimumBins K : ℝ)) ∧
        (∃ stripProgram : ScalarProgram, ∃ c d : ℕ, 0 < c ∧
          ∀ K : PackingInput, AdmissibleInput K → WidthsAtMost (1 - δ) K →
            (∃ time out, StripExecution stripProgram K time out ∧
              time ≤ c * (packingInputSize K + 1) ^ d) ∧
            ∀ time out, StripExecution stripProgram K time out →
              StripFeasible K out ∧
              out.height ≤ Cstrip * α K.length / δ ^ 2 * optimumHeight K) := by sorry

end PolyhedralPacking1261.Packing.Supplement
