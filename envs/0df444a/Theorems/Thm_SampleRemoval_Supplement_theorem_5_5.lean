-- Prove2me | Theorems.Thm_SampleRemoval_Supplement_theorem_5_5
-- name    : SampleRemoval.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:23:41.192387+00:00
-- url     : https://prove2.me/theorems/67161580-10ef-4b22-b210-9ea34ad793b3
-- title:
--   Theorem 5.5 — ranges do not suffice for audits
-- statement:
--   For the twelve points displayed in Theorem 5.5, the data are in GP and LGP and the full-sample cross-scatter is positive. Every eleven-point retained set has positive cross-scatter. Exactly one ten-point set has nonpositive cross-scatter, namely $[12]\setminus\{p_1,p_5\}$, so
--
--   $$s_{\mathrm{int}}=2.$$
--
--   That ten-set is not a lifted-plane range. Equivalently, every lifted-plane range that makes the slope nonpositive must delete at least three observations, so any method restricted to this range family reports at least three deletions.
--
--   Differences from the source:
--   - encoding: printed terminating decimals and one-based point labels → exact rational real coordinates and zero-based `Fin 12` indices; reason: this changes no mathematical instance and makes every strict sign and uniqueness claim exact
--   - reading: every method that outputs only lifted-plane ranges reports at least three deletions → every lifted-plane range with defined nonpositive slope retains at most nine points; reason: this is the direct method-independent mathematical content of the stated consequence
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Theorem 5.5, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_SampleRemoval_GeneralPosition
import Definitions.Def_SampleRemoval_sInt
import Definitions.Def_SampleRemoval_Supplement_simpleDesign
import Definitions.Def_SampleRemoval_Supplement_crossScatter
import Definitions.Def_SampleRemoval_Supplement_IsLGP
import Definitions.Def_SampleRemoval_Supplement_IsLiftedPlaneRangeOn
import Definitions.Def_SampleRemoval_Supplement_points55

set_option autoImplicit false

namespace SampleRemoval.Supplement

/-- **Theorem 5.5 (Ranges do not suffice for audits).** The displayed exact twelve-point
instance is in GP and LGP with positive full-sample cross-scatter. Every eleven-set has positive
cross-scatter; the unique nonpositive ten-set deletes `p₁,p₅`, so integral stability is two;
that ten-set is not a lifted-plane range, and every feasible lifted-plane range deletes at least
three points (Xu, Gao, Hu, STOC 2027 submission, manuscript sha256 `dcd33ace…`, Theorem 5.5,
p.11 (PDF p.13)).

**Formalization Note** Paper indices are one-based, so the unique ten-set omits Lean indices
`0,4`. Printed decimals in `points55` are exact rationals. `sInt` is the published base mission's
integral stability for the intercept-plus-regressor design, response `y`, second-coordinate
direction, and threshold zero. The final universal clause is the precise mathematical content
of the paper's consequence for every method restricted to lifted-plane ranges. -/
theorem theorem_5_5 :
    let S : Finset (Fin 12) := Finset.univ.filter (fun i => i.1 ≠ 0 ∧ i.1 ≠ 4)
    let e : Fin 2 → ℝ := fun j => if j.1 = 1 then 1 else 0
    SampleRemoval.GeneralPosition (simpleDesign points55) ∧
    IsLGP points55 ∧
    0 < crossScatter points55 Finset.univ ∧
    (∀ T : Finset (Fin 12), T.card = 11 → 0 < crossScatter points55 T) ∧
    S.card = 10 ∧ crossScatter points55 S ≤ 0 ∧
    (∀ T : Finset (Fin 12), T.card = 10 →
      (crossScatter points55 T ≤ 0 ↔ T = S)) ∧
    SampleRemoval.sInt (simpleDesign points55) (fun i => (points55 i).2) e 0 = 2 ∧
    ¬ IsLiftedPlaneRangeOn points55 Finset.univ S ∧
    (∀ T : Finset (Fin 12), IsLiftedPlaneRangeOn points55 Finset.univ T →
      2 ≤ T.card → crossScatter points55 T ≤ 0 → 3 ≤ 12 - T.card) := by sorry

end SampleRemoval.Supplement
