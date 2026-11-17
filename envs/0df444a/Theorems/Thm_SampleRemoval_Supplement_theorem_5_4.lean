-- Prove2me | Theorems.Thm_SampleRemoval_Supplement_theorem_5_4
-- name    : SampleRemoval.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:23:05.637025+00:00
-- url     : https://prove2.me/theorems/5018164c-85aa-49b5-8ac3-1d4078b0b41c
-- title:
--   Theorem 5.4 — integral optima need not be ranges
-- statement:
--   For the six points displayed in Theorem 5.4, the intercept-plus-regressor design is in GP and the saddle lifts are in LGP. Among all four-element retained sets, $S=\{p_2,p_3,p_5,p_6\}$ is the unique minimizer of cross-scatter, with
--
--   $$F(S)=-\frac{37469}{8000}.$$
--
--   The next smallest value is attained and equals $-185881/40000$. Nevertheless, no strict plane cut of the saddle lifts selects exactly $S$; the unique integral optimum is not a lifted-plane range.
--
--   Differences from the source:
--   - encoding: printed terminating decimals and one-based point labels → exact rational real coordinates and zero-based `Fin 6` indices; reason: this changes no mathematical instance and makes every equality and strict inequality exact
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Theorem 5.4, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_SampleRemoval_GeneralPosition
import Definitions.Def_SampleRemoval_Supplement_simpleDesign
import Definitions.Def_SampleRemoval_Supplement_crossScatter
import Definitions.Def_SampleRemoval_Supplement_IsLGP
import Definitions.Def_SampleRemoval_Supplement_IsLiftedPlaneRangeOn
import Definitions.Def_SampleRemoval_Supplement_points54

set_option autoImplicit false

namespace SampleRemoval.Supplement

/-- **Theorem 5.4 (Integral optima need not be ranges).** The displayed exact six-point instance
is in GP and LGP; `{p₂,p₃,p₅,p₆}` uniquely minimizes `F` over four-sets, has the stated
value and next-best value, and is not a lifted-plane range (Xu, Gao, Hu, STOC 2027 submission,
manuscript sha256 `dcd33ace…`, Theorem 5.4, p.10 (PDF p.12)).

**Formalization Note** The paper's indices are one-based; `S` therefore uses Lean indices
`1,2,4,5`. Printed decimals in `points54` are exact terminating rationals in `ℝ`. The next
smallest value is stated by both attainment and a lower bound over every competing four-set,
avoiding any empty-infimum convention. -/
theorem theorem_5_4 :
    let S : Finset (Fin 6) := Finset.univ.filter (fun i => i.1 = 1 ∨ i.1 = 2 ∨ i.1 = 4 ∨ i.1 = 5)
    SampleRemoval.GeneralPosition (simpleDesign points54) ∧
    IsLGP points54 ∧
    S.card = 4 ∧
    crossScatter points54 S = -(37469 : ℝ) / 8000 ∧
    (∀ T : Finset (Fin 6), T.card = 4 → T ≠ S →
      crossScatter points54 S < crossScatter points54 T) ∧
    (∃ T : Finset (Fin 6), T.card = 4 ∧ T ≠ S ∧
      crossScatter points54 T = -(185881 : ℝ) / 40000) ∧
    (∀ T : Finset (Fin 6), T.card = 4 → T ≠ S →
      -(185881 : ℝ) / 40000 ≤ crossScatter points54 T) ∧
    ¬ IsLiftedPlaneRangeOn points54 Finset.univ S := by sorry

end SampleRemoval.Supplement
