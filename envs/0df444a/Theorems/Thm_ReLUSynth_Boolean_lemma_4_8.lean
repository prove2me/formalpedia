-- Prove2me | Theorems.Thm_ReLUSynth_Boolean_lemma_4_8
-- name    : ReLUSynth.Boolean.lemma_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:11:48.584203+00:00
-- url     : https://prove2.me/theorems/0e7cc20e-1d06-429c-a9dd-658c89ae05a6
-- title:
--   Lemma 4.8 — full-target tests: f monotone, every coordinate essential, f(0) = f(e_j) = 0, nonminimal winners span, a mixed difference −1
-- statement:
--   For the calibrated target $f$: $f$ is monotone; every coordinate is essential; $f(0)=f(e_j)=0$ for every coordinate $j$; the nonminimal winning vertices (winning vertices from which deleting one selected coordinate still gives a winning vertex) affinely span $\mathbb R^d$; and $f$ has a pairwise mixed difference
--   $$f(1,1)-f(1,0)-f(0,1)+f(0,0)=-1$$
--   on some two-coordinate Boolean face.
--
--   These properties of the target are what the placement argument (Lemma 4.9) uses after the graph is constrained.
--
--   Differences from the source:
--   - generalization: an instance in the hardness family produced by Lemma 4.5 (p. 19) → any instance satisfying every restriction listed in Lemma 4.5 (CalibData.Valid: q ≥ 5 prime, 0 < β_j < T, β_j not a power of two, β_j ≡ 3, T ≡ 0 (mod q), n > p); reason: the proofs on pp. 19–27 and in Appendix A use only these restrictions; every instance the reduction produces satisfies them, so the Lean statement specializes to the paper's
--   - reading: choose an odd prime r, powers of two F and M satisfying the displayed inequalities (pp. 19–20) → every choice of r, F, M satisfying those inequalities (strictly, as printed); reason: the page leaves the choice free among the values satisfying the inequalities, and its lemmas are claimed for the construction so chosen
--   - encoding: the nonminimal winning vertices affinely span R^d → affineSpan ℝ of the set of their 0/1 vectors in Coord c → ℝ is ⊤; reason: the coordinates are indexed by the type Coord c of the d coordinates
-- source:
--   Myrisiotis, The Complexity of ReLU Network Synthesis from a Parameter Multiset, arXiv:2611.04074v1, p. 23, Lemma 4.8

import Mathlib
import Definitions.Def_ReLUSynth_Boolean_Calibrated

namespace ReLUSynth.Boolean

/-- Lemma 4.8 (p. 23): the calibrated target `f` is monotone, every coordinate is essential,
`f(0) = f(e_j) = 0` for every coordinate `j`, the nonminimal winning vertices (winners from which
deleting some selected coordinate still wins) affinely span `ℝ^d`, and `f` has a pairwise mixed
difference of `−1` on a Boolean face. -/
theorem lemma_4_8 (c : CalibData) (hc : c.Valid) :
    Monotone c.target ∧
    (∀ t : Coord c, ∃ x : Coord c → Bool,
      c.target (Function.update x t false) ≠ c.target (Function.update x t true)) ∧
    c.target (fun _ => false) = false ∧
    (∀ t : Coord c, c.target (fun s => decide (s = t)) = false) ∧
    affineSpan ℝ {v : Coord c → ℝ | ∃ x : Coord c → Bool, v = boolVec x ∧ c.target x = true ∧
      ∃ t, x t = true ∧ c.target (Function.update x t false) = true} = ⊤ ∧
    ∃ (s t : Coord c) (x : Coord c → Bool), s ≠ t ∧
      mixedDiff (fun y => bitR (c.target y)) s t x = -1 := by sorry

end ReLUSynth.Boolean
