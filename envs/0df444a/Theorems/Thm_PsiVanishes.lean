-- Prove2me | Theorems.Thm_PsiVanishes
-- name    : PsiVanishes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:58:50.53951+00:00
-- url     : https://prove2.me/theorems/4c33f066-4cf5-4af1-8e73-2136c6fe2bac
-- title:
--   Psi Vanishes: Psi Vanishes
-- statement:
--   Paper Lemma A.3 (paper.tex 1817), threshold form: given a countable dense `D`, a bound `C`,
--   a length `l`, and a finite measure `η` on `Θ(E)` concentrated (a.e.) on curves of length `l`, for
--   every `θ > 0` there is an admissible index `(m, Q, ε)` — `1 ≤ m`, `Q` a nonempty finite subset of
--   `D`, `ε` a positive *rational* (paper.tex 1292: the countable admissible family ranges over
--   `ε, C ∈ ℚ ∩ (0,∞)`) — at which `ψ_{m,Q,ε,C}` and `ψ̃_{m,Q,ε,C}` are both `η`-integrable and their
--   `η`-integrals sum to less than `θ`. This replaces the paper's iterated limit
--   `lim_m lim_Q lim_ε (…) = 0` by a single threshold witness, which is what the diagonal argument
--   downstream (`SLLNCurves`/`BBSamplingDiagonal`) actually consumes. `D.Nonempty` is an added
--   hypothesis making explicit an assumption the paper's ambient separable metric space `E` carries
--   implicitly (see the `.tex` for why the theorem is otherwise false when `E`/`D` may be empty).
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PsiVanishes.lean#L19-L273
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PsiVanishes.lean#L19-L273

import Definitions.Def_Tablet_psi
import Definitions.Def_Tablet_psiTilde
import Definitions.Def_Tablet_PsiMeasurable
import Definitions.Def_Tablet_PsiTildeMeasurable
import Definitions.Def_Tablet_PsiVanishes
import Theorems.Thm_PsiMeasurable
import Theorems.Thm_PsiTildeMeasurable

set_option autoImplicit false
open MeasureTheory Filter Topology

theorem PsiVanishes {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (D : Set E) (hDc : D.Countable) (hDne : D.Nonempty) (hDd : Dense D)
    (C : ℝ) (hC : 0 < C) (l : ℕ)
    (η : Measure (Curve E)) [IsFiniteMeasure η]
    (hlen : ∀ᵐ γ ∂η, γ.len = (l : ℝ))
    (θ : ℝ) (hθ : 0 < θ) :
    ∃ (m : ℕ) (Q : Finset E) (ε : ℚ),
      1 ≤ m ∧ Q.Nonempty ∧ (Q : Set E) ⊆ D ∧ 0 < ε ∧
      Integrable (fun γ : Curve E => psi m Q (ε : ℝ) C γ) η ∧
      Integrable (fun γ : Curve E => psiTilde m Q (ε : ℝ) C γ) η ∧
      (∫ γ, psi m Q (ε : ℝ) C γ ∂η) + (∫ γ, psiTilde m Q (ε : ℝ) C γ ∂η) < θ := by sorry
