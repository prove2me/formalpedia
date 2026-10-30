-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_boundIncomparability
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.boundIncomparability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:42:41.323606+00:00
-- url     : https://prove2.me/theorems/67ac1163-80a4-4892-8490-d63bdd6038c8
-- title:
--   Sections V A and VI: comparison of the two operational bounds
-- statement:
--   Among positive finite-dimensional CPTP function computations with an ideal map that has zero worst-case error for the specified function, both $D_{\rm stab}<C_{\rm stab}^2$ and $D_{\rm stab}>C_{\rm stab}^2$ occur. Moreover, for function computation with computational-basis inputs and outputs, let $e_U$ be the actual worst-case ideal function error for a unitary ideal $U$. There exist real CPTP maps and such ideal computations with each strict ordering
--
--   $$e_U+D_{\rm stab}(\mathcal E,U)<(\sqrt{e_U}+C_{\rm stab}(\mathcal E,U))^2,$$
--
--   $$e_U+D_{\rm stab}(\mathcal E,U)>(\sqrt{e_U}+C_{\rm stab}(\mathcal E,U))^2.$$
--
--   The witnesses in the two comparisons may differ, and intrinsic ideal error is permitted. Neither operational bound is universally the stronger one.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 12, Sections V A and VI: comparison of the two operational bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P17

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Advance50.P17

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P75 (hermitianReal)

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]
  [Nonempty I] [Nonempty J] [Nonempty K]

/-- Sections V A and VI, PDF pp.9,12: both orderings of D_stab and C_stab squared occur
with zero ideal function error; both orderings of the complete function-error bounds occur
even with a unitary ideal.
The second comparison includes the actual intrinsic ideal function error. -/
theorem boundIncomparability :
    (∃ d : ℕ, ∃ hd : 0 < d, letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
      ∃ E F : FiniteProcess (Fin d) (Fin d), ∃ f : Fin d → Fin d,
        worstFunctionErrorProbability F.val f = 0 ∧
        stabDistance (stateDistance .trace) E.val F.val < stabC E.val F.val ^ 2) ∧
    (∃ d : ℕ, ∃ hd : 0 < d, letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
      ∃ E F : FiniteProcess (Fin d) (Fin d), ∃ f : Fin d → Fin d,
        worstFunctionErrorProbability F.val f = 0 ∧
        stabC E.val F.val ^ 2 < stabDistance (stateDistance .trace) E.val F.val) ∧
    (∃ d : ℕ, ∃ hd : 0 < d, letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
      ∃ E : FiniteProcess (Fin d) (Fin d), ∃ U : Matrix.unitaryGroup (Fin d) ℂ, ∃ f : Fin d → Fin d,
        let ideal := conjSuperop (U : Matrix (Fin d) (Fin d) ℂ)
        worstFunctionErrorProbability ideal f + stabDistance (stateDistance .trace) E.val ideal <
          (Real.sqrt (worstFunctionErrorProbability ideal f) + stabC E.val ideal) ^ 2) ∧
    (∃ d : ℕ, ∃ hd : 0 < d, letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
      ∃ E : FiniteProcess (Fin d) (Fin d), ∃ U : Matrix.unitaryGroup (Fin d) ℂ, ∃ f : Fin d → Fin d,
        let ideal := conjSuperop (U : Matrix (Fin d) (Fin d) ℂ)
        (Real.sqrt (worstFunctionErrorProbability ideal f) + stabC E.val ideal) ^ 2 <
          worstFunctionErrorProbability ideal f + stabDistance (stateDistance .trace) E.val ideal) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
