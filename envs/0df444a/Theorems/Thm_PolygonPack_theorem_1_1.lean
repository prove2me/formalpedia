-- Prove2me | Theorems.Thm_PolygonPack_theorem_1_1
-- name    : PolygonPack.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:54.097784+00:00
-- url     : https://prove2.me/theorems/bba66477-c703-4fb7-b905-6356c7b3b41a
-- title:
--   Theorem 1.1 — (17/3+2√2+ε)-approximation for weighted convex-polygon knapsack
-- statement:
--   Let $\varepsilon>0$. There is a function $f$, computed by a Turing machine in time polynomial in the binary length of its input, with the following property. For every instance of convex polygons of positive area with rational vertices, each fitting alone in the unit square, with nonnegative rational profits, $f$ returns exact algebraic poses that pack a subset of polygons in the unit square under rotations and translations, and the profit $V$ of that subset satisfies
--   $$
--   \pi(S')\le\Bigl(\frac{17}3+2\sqrt2+\varepsilon\Bigr)V
--   $$
--   for every subset $S'$ that can be packed in the unit square.
--
--   This is the paper's main theorem for knapsack, and the first polynomial-time constant-factor approximation in the unrestricted binary-input model under arbitrary rotations.
--
--   Differences from the source:
--   - reading: deterministic polynomial-time algorithm → one function f after ε, with Nonempty (Turing.TM2ComputableInPolyTime encInstance encOut f); reason: p.13 measures time in the total binary encoding length, and p.54 lets the exponent depend on ε
--   - reading: placements returned as exact real algebraic numbers of polynomial description length → each pose number as a nonzero integer polynomial with a rational interval isolating its root; reason: the per-coordinate form of p.48; description length follows from the time bound
--   - generalization: convex polygons given by their vertices → the convex hull of any finite rational vertex list, in any order; reason: the vertices of a convex polygon are such a list
--   - reading: convex polygons (p.1) → polygons of positive area; reason: the paper assumes positive area on p.46; the degenerate extension there is optional
--   - encoding: the profit of a feasible comparison packing, or of OPT → a bound for every feasible subset S'; reason: subsets are finite, so an optimum exists and this is the same bound, also when its profit is zero
--   - encoding: (17/3 + 2√2 + ε) ≈ 8.5 → the exact real constant; "≈ 8.5" is omitted; reason: p.54 treats 8.5 as a remark that holds for small ε
--   - encoding: every fixed constant ε > 0 → every real ε > 0; reason: the proof picks smaller rational accuracies, p.51 and p.52
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Theorem 1.1, p.2; proof, p.52

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_PolygonPack_Instance
import Definitions.Def_PolygonPack_Pose
import Definitions.Def_PolygonPack_Packs
import Definitions.Def_PolygonPack_Instance_Valid
import Definitions.Def_PolygonPack_AlgNum
import Definitions.Def_PolygonPack_Out
import Definitions.Def_PolygonPack_encInstance
import Definitions.Def_PolygonPack_encOut

namespace PolygonPack

/-- **Theorem 1.1.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), p.2; proof p.52. "For every fixed constant ε > 0, there is a deterministic polynomial-time (17/3+2√2+ε) ≈ 8.5-approximation algorithm for weighted convex-polygon knapsack in a unit square,
allowing arbitrary rotations and translations."

For every `ε > 0` there is one function `f`, computed by a polynomial-time Turing machine from binary instances to exact algebraic packings, such that on every valid instance the output is a sound packing and
`π(S') ≤ (17/3 + 2√2 + ε)·π(output)` for every feasible `S'`.

**Formalization Note.** "Polynomial time" is `Turing.TM2ComputableInPolyTime` on the binary encoders `encInstance`, `encOut`, as p.13 measures it ("the total binary encoding length of the input vertices and profits"), and
"deterministic" is the machine computing a function. The exponent may depend on `ε` (p.54), so `f` comes after `ε`. The approximation is stated against every feasible `S'` rather than a named optimum: subsets are
finite, so this is equivalent, and it also covers `π(OPT) = 0`. "≈ 8.5" is a remark (p.54) and is not claimed. The constant is real, with `√2` written exactly. -/
theorem theorem_1_1 (ε : ℝ) (hε : 0 < ε) :
    ∃ f : Instance → Out, Nonempty (Turing.TM2ComputableInPolyTime encInstance encOut f) ∧
      ∀ I : Instance, I.Valid → (f I).Sound I ∧
        ∀ S' : Finset (Fin I.n), Feasible I S' →
          profit I S' ≤ (17 / 3 + 2 * Real.sqrt 2 + ε) * profit I ((f I).indexSet I) := by sorry

end PolygonPack
