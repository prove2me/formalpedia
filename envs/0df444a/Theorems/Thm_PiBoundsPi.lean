-- Prove2me | Theorems.Thm_PiBoundsPi
-- name    : PiBoundsPi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:57:00.336941+00:00
-- url     : https://prove2.me/theorems/6c85f668-b286-4185-a870-4c978544a230
-- title:
--   Pi Bounds Pi: Pi Bounds Pi
-- statement:
--   Paper Lemma A.2, eq. (pi_estimate) (paper.tex line 1727): replacing `π` by `π - π'` inside a
--   metric `1`-form's current against `γ` is controlled by `ψ_{m,Q,ε,C}(γ)` (`psi`). Requires
--   `1 ≤ m` and `Q.Nonempty` (see the node's `.tex` for why the paper's literal transcription is
--   vacuous, and can even be false, without them).
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PiBoundsPi.lean#L14-L174
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PiBoundsPi.lean#L14-L174

import Definitions.Def_Tablet_psi
import Definitions.Def_Tablet_PartitionChordSum
import Definitions.Def_Tablet_CurrentChordEstimate
import Definitions.Def_Tablet_CurrentResolutionAdditive
import Definitions.Def_Tablet_RestrictCurrentFormula
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_PiBoundsPi
import Theorems.Thm_CurrentChordEstimate
import Theorems.Thm_CurrentResolutionAdditive
import Theorems.Thm_PartitionChordSum
import Theorems.Thm_RestrictCurrentFormula

set_option autoImplicit false

theorem PiBoundsPi {E : Type*} [MetricSpace E] (γ : Curve E) (m : ℕ) (hm : 1 ≤ m)
    (Q : Finset E) (hQne : Q.Nonempty) (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C)
    (ω ω' : Form1 E)
    (hfB : (ω.fBound : ℝ) ≤ C) (hfL : (ω.fLip : ℝ) ≤ C)
    (hpL : (ω.piLip : ℝ) ≤ C) (hpL' : (ω'.piLip : ℝ) ≤ C)
    (hQ : ∀ q ∈ Q, |ω.pi q - ω'.pi q| ≤ ε) :
    |curveCurrent γ
        { f := ω.f, fBound := ω.fBound, f_bounded := ω.f_bounded,
          fLip := ω.fLip, f_lipschitz := ω.f_lipschitz,
          pi := fun x => ω.pi x - ω'.pi x,
          piLip := ω.piLip + ω'.piLip,
          pi_lipschitz := ω.pi_lipschitz.sub ω'.pi_lipschitz }|
      ≤ psi m Q ε C γ := by sorry
