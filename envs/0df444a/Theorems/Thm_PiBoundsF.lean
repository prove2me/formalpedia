-- Prove2me | Theorems.Thm_PiBoundsF
-- name    : PiBoundsF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:56:31.639927+00:00
-- url     : https://prove2.me/theorems/b3931bda-042b-5a5e-8d53-0d6e8768f8ef
-- title:
--   Pi Bounds F: Pi Bounds F
-- statement:
--   Paper Lemma A.2, eq. (f_estimate) (paper.tex line 1728): replacing `f` by `f - f'` inside a
--   metric `1`-form's current against `γ` is controlled by `ψ̃_{m,Q,ε,C}(γ)` (`psiTilde`). Requires
--   `1 ≤ m` and `Q.Nonempty`, for the same reason as `PiBoundsPi` (see the node's `.tex`).
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PiBoundsF.lean#L13-L174
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PiBoundsF.lean#L13-L174

import Definitions.Def_Tablet_psiTilde
import Definitions.Def_Tablet_PartitionChordSum
import Definitions.Def_Tablet_CurrentChordEstimate
import Definitions.Def_Tablet_CurrentResolutionAdditive
import Definitions.Def_Tablet_RestrictCurrentFormula
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_PiBoundsF
import Theorems.Thm_CurrentChordEstimate
import Theorems.Thm_CurrentResolutionAdditive
import Theorems.Thm_PartitionChordSum
import Theorems.Thm_RestrictCurrentFormula

set_option autoImplicit false

theorem PiBoundsF {E : Type*} [MetricSpace E] (γ : Curve E) (m : ℕ) (hm : 1 ≤ m)
    (Q : Finset E) (hQne : Q.Nonempty) (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C)
    (ω ω' : Form1 E)
    (hfB : (ω.fBound : ℝ) ≤ C) (hfB' : (ω'.fBound : ℝ) ≤ C)
    (hfL : (ω.fLip : ℝ) ≤ C) (hfL' : (ω'.fLip : ℝ) ≤ C)
    (hpL : (ω.piLip : ℝ) ≤ C)
    (hQ : ∀ q ∈ Q, |ω.f q - ω'.f q| ≤ ε) :
    |curveCurrent γ
        { f := fun x => ω.f x - ω'.f x,
          fBound := ω.fBound + ω'.fBound,
          f_bounded := fun x => (abs_sub _ _).trans
            (by push_cast; exact add_le_add (ω.f_bounded x) (ω'.f_bounded x)),
          fLip := ω.fLip + ω'.fLip,
          f_lipschitz := ω.f_lipschitz.sub ω'.f_lipschitz,
          pi := ω.pi, piLip := ω.piLip, pi_lipschitz := ω.pi_lipschitz }|
      ≤ psiTilde m Q ε C γ := by sorry
