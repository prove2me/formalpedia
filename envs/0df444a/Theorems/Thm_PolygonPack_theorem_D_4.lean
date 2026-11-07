-- Prove2me | Theorems.Thm_PolygonPack_theorem_D_4
-- name    : PolygonPack.theorem_D_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:58:26.212508+00:00
-- url     : https://prove2.me/theorems/6237d8b8-5e70-49ed-83ab-1a9e58feb3c1
-- title:
--   Theorem D.4 — Short candidate
-- statement:
--   For each $\varepsilon_S>0$ there is a cutoff $\bar a>0$ such that, for every rational $a_0$ with $0<a_0\le\bar a$, a polynomial-time machine returns on every valid instance a sound packing of Short polygons, of profit $V$, with
--   $$
--   \pi(S')\le\Bigl(\frac83+\varepsilon_S\Bigr)V
--   $$
--   for every feasible family $S'$ of Short polygons.
--
--   This is the candidate for short polygons in the final algorithm.
--
--   Differences from the source:
--   - generalization: a fixed positive cutoff for a0 suffices → one machine per rational a0 ≤ ā, for all such a0; reason: the proof gives an upper bound on a0 on p.44; rationals are dense, so a fixed cutoff is an instance
--   - encoding: the profit of a feasible comparison packing, or of OPT → a bound for every feasible subset S'; reason: subsets are finite, so an optimum exists and this is the same bound, also when its profit is zero
--   - reading: polynomial time in the total binary encoding length → Nonempty (Turing.TM2ComputableInPolyTime …) on the fixed binary encoders; reason: p.13 names this measure; the paper fixes no machine model
--   - reading: placements returned as exact real algebraic numbers of polynomial description length → each pose number as a nonzero integer polynomial with a rational interval isolating its root; reason: the per-coordinate form of p.48; description length follows from the time bound
--   - generalization: convex polygons given by their vertices → the convex hull of any finite rational vertex list, in any order; reason: the vertices of a convex polygon are such a list
--   - reading: convex polygons (p.1) → polygons of positive area; reason: the paper assumes positive area on p.46; the degenerate extension there is optional
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Theorem D.4, p.44; proof, pp.44–45

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_PolygonPack_Instance
import Definitions.Def_PolygonPack_Pose
import Definitions.Def_PolygonPack_Packs
import Definitions.Def_PolygonPack_Instance_Valid
import Definitions.Def_PolygonPack_diag
import Definitions.Def_PolygonPack_eucl
import Definitions.Def_PolygonPack_thick
import Definitions.Def_PolygonPack_diamPair
import Definitions.Def_PolygonPack_polyArea
import Definitions.Def_PolygonPack_placedUV
import Definitions.Def_PolygonPack_canonBottom
import Definitions.Def_PolygonPack_IsTight
import Definitions.Def_PolygonPack_Kc
import Definitions.Def_PolygonPack_AlgNum
import Definitions.Def_PolygonPack_Out
import Definitions.Def_PolygonPack_encInstance
import Definitions.Def_PolygonPack_encOut

namespace PolygonPack

/-- **Theorem D.4 (Short candidate).** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), p.44. "For each ε_S > 0, a fixed positive cutoff for a0 suffices for a polynomial-time algorithm to return a packing of Short polygons of profit at least
W_S/(8/3 + ε_S), for every feasible comparison family of Short polygons of profit W_S."

**Formalization Note.** The proof asks for `a0 ≤ min{τ, β(τ)²}/(2(1 + τ)²)` (p.44), an upper bound, so the Lean quantifies over every rational `a0` up to a cutoff `ā` that depends only on `ε_S`. `a0` is
rational because the machine classifies with it exactly (p.47). -/
theorem theorem_D_4 (εS : ℝ) (hεS : 0 < εS) :
    ∃ abar : ℝ, 0 < abar ∧ ∀ a0 : ℚ, 0 < a0 → (a0 : ℝ) ≤ abar →
      ∃ f : Instance → Out, Nonempty (Turing.TM2ComputableInPolyTime encInstance encOut f) ∧
        ∀ I : Instance, I.Valid → (f I).Sound I ∧ (∀ i ∈ (f I).indexSet I, IsShort a0 (I.verts i)) ∧
          ∀ S' : Finset (Fin I.n), Feasible I S' → (∀ i ∈ S', IsShort a0 (I.verts i)) →
            profit I S' ≤ (8 / 3 + εS) * profit I ((f I).indexSet I) := by sorry

end PolygonPack
