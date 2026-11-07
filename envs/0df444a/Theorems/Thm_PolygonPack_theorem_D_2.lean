-- Prove2me | Theorems.Thm_PolygonPack_theorem_D_2
-- name    : PolygonPack.theorem_D_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:55:33.055212+00:00
-- url     : https://prove2.me/theorems/2994d9a7-4b54-4f58-96a2-6e51852e5240
-- title:
--   Theorem D.2 — three-quarter area packing
-- statement:
--   For each $0<\zeta<3/4$ there is $\beta>0$ such that any rectangles with $0<z_i\le r_i\le1$, $z_i\le\beta$ and
--   $$
--   \sum_ir_iz_i\le\frac34-\zeta
--   $$
--   can be packed in the unit square by translations and quarter turns. For rational dimensions, a polynomial-time machine, fixed once $\zeta$ is, computes such a packing.
--
--   This packing theorem turns an area budget of $3/4-\zeta$ into a feasible packing of thin rectangles, and it is the source of the factor $8/3$.
--
--   Differences from the source:
--   - encoding: the construction takes polynomial time for rational dimensions → a machine on rational lists, correct for inputs meeting the hypotheses; reason: the machine is total
--   - reading: polynomial time in the total binary encoding length → Nonempty (Turing.TM2ComputableInPolyTime …) on the fixed binary encoders; reason: p.13 names this measure; the paper fixes no machine model
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Theorem D.2, p.42

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_PolygonPack_encInstance
import Definitions.Def_PolygonPack_IsRectPacking

namespace PolygonPack

/-- **Theorem D.2 (Three-quarter area packing).** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), p.42. "For each fixed 0 < ζ < 3/4, there exists β(ζ) > 0 with the following property. Rectangles with 0 < z_i ≤ r_i ≤ 1, z_i ≤ β(ζ), and total area at
most 3/4 − ζ can be packed in a unit square by translations and quarter turns. For rational dimensions the construction takes polynomial time in the total binary input length."

The threshold `β` comes before the rectangles, and it and the machine depend on `ζ` only.

**Formalization Note.** The output is a list aligned with the input, one entry `(rot, x, y)` per rectangle. A machine is total, so correctness is claimed only for inputs meeting the hypotheses. -/
theorem theorem_D_2 (ζ : ℝ) (hζ : 0 < ζ) (hζ' : ζ < 3 / 4) :
    ∃ β : ℝ, 0 < β ∧
      (∀ (n : ℕ) (r z : Fin n → ℝ), (∀ i, 0 < z i ∧ z i ≤ r i ∧ r i ≤ 1 ∧ z i ≤ β) → ∑ i, r i * z i ≤ 3 / 4 - ζ →
        ∃ (rot : Fin n → Bool) (x y : Fin n → ℝ), IsRectPacking r z rot x y) ∧
      ∃ f : List (ℚ × ℚ) → List (Bool × ℚ × ℚ), Nonempty (Turing.TM2ComputableInPolyTime encRects encRectOut f) ∧
        ∀ L : List (ℚ × ℚ),
          (∀ R ∈ L, 0 < R.2 ∧ R.2 ≤ R.1 ∧ R.1 ≤ 1 ∧ ((R.2 : ℚ) : ℝ) ≤ β) →
          (((L.map (fun R => R.1 * R.2)).sum : ℚ) : ℝ) ≤ 3 / 4 - ζ →
          ∃ hlen : (f L).length = L.length,
            IsRectPacking (fun i : Fin L.length => (((L.get i).1 : ℚ) : ℝ)) (fun i => (((L.get i).2 : ℚ) : ℝ))
              (fun i => ((f L).get (Fin.cast hlen.symm i)).1)
              (fun i => ((((f L).get (Fin.cast hlen.symm i)).2.1 : ℚ) : ℝ))
              (fun i => ((((f L).get (Fin.cast hlen.symm i)).2.2 : ℚ) : ℝ)) := by sorry

end PolygonPack
