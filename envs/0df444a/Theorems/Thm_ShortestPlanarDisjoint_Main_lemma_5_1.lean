-- Prove2me | Theorems.Thm_ShortestPlanarDisjoint_Main_lemma_5_1
-- name    : ShortestPlanarDisjoint.Main.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:41:05.933953+00:00
-- url     : https://prove2.me/theorems/412216c1-03f2-48b8-b298-c590b858d4c4
-- title:
--   Lemma 5.1 — Seam construction
-- statement:
--   For the connected nontrivial planar instance of Section 4 and any selected terminal-free boundary gaps, a logspace-uniform NC² family constructs finite seams and their ordered crossing lists. There is one absolute coefficient A such that the total number of intersections is at most A n f. With r=f−1, cutting produces a disk with f+2r=3f−2 sides and contiguous terminal blocks. Each seam goes from its nonroot face gap to the root gap. After relabelling, the disk boundary is exactly B_1,a_1,B_2,b_1,...,a_r,B_f,b_r as in (1). Its seam copies have reversed boundary-order identification. The output includes the actual polygonal seam code. No disk cut is assumed of the input embedding.
--
--   Differences from the source:
--   - encoding: a supplied cellular embedding with corner assignments on a connected surface → a Fin-indexed signed rotation flag map with computed integer Euler genus, explicit corners and used-face labels; reason: this is the same finite cellular embedding up to barycentric realization, including both orientable and nonorientable cases; connectedness is necessary for cellularity, and isolated single-vertex spheres are retained
--   - encoding: seams, a cut disk and NC² construction → rational polygonal curves on the realized surface, RealizesCut and actual uniformly generated Boolean circuits; reason: finite subdivisions and parallel tracks represent the source construction; Section 4's connectedness and k>0 are explicit, and all topological and crossing properties are conclusions
--   - encoding: uniform O bounds with fixed weight exponent and fixed logarithmic coefficient → uniform natural coefficients and exponents before instance data, N=max(2,n), k≤c ceil(log₂ N), and ceil(log₂(1/δ)) repetition envelopes; reason: natural exponents cover every fixed real exponent by rounding up; small cases have finite envelopes; no witness depends on a graph, optimum or random tape
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Lemma 5.1, p. 15 (PDF p. 17)

import Definitions.Def_ShortestPlanarDisjoint_Main_Seams
set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main
/-- Uniform NC² constructs actual finite polygonal seams and their ordered
crossing lists. RealizesCut supplies the disk, contiguous terminal blocks and
fixed side identifications as conclusions, not an embedding certificate field. -/
theorem lemma_5_1 :
    ∃ (F : UniformCircuitFamily) (A d : ℕ),
      LogspaceUniform F A d ∧
      (∀ n, (F.circuit n).size ≤ A * (max 2 n) ^ d ∧
        (F.circuit n).depth ≤ A * (logEnvelope n) ^ 2) ∧
      ∀ (n k f : ℕ) (I : RoutingInput n k) (E : FaceInput I f) (gaps : E.GapChoice),
        0 < k → E.IsCellular → E.embedding.IsPlanar →
        let input := E.bits ++ gaps.bits
        input.length ≤ (F.circuit n).inputs ∧
        ∃ S : SeamCode E (f-1), S.RealizesCut gaps ∧ S.PlanarOrder gaps ∧
          S.crossingCount ≤ A * n * f ∧
          S.layout.sideOrder.length = f + 2 * (f-1) ∧
          S.layout.sideOrder.length = 3*f-2 ∧
          (∀ s, S.sameOrder s = false) ∧
          S.bits.IsPrefix ((F.circuit n).eval
            (input ++ List.replicate ((F.circuit n).inputs-input.length) false)) := by sorry
end ShortestPlanarDisjoint.Main
