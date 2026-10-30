-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_pureMixed
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.pureMixed
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:32:34.824044+00:00
-- url     : https://prove2.me/theorems/49ce6f42-c3cb-4aae-8e55-1a8d3fb569ce
-- title:
--   Section IV C: pure inputs suffice for worst-case optimization
-- statement:
--   Let $\mathcal E,\mathcal F$ be CPTP maps on a positive finite-dimensional register. For each $\Delta\in\{D,A,B,C\}$, its pure-input supremum is attained by a unit vector $\psi$, and
--
--   $$\max_{\rho\text{ density}}\Delta(\mathcal E(\rho),\mathcal F(\rho))=\Delta(\mathcal E(\psi),\mathcal F(\psi))=\max_{\phi\text{ pure}}\Delta(\mathcal E(\phi),\mathcal F(\phi)).$$
--
--   Likewise, the minimum squared fidelity over all density inputs equals its pure-input minimum and has a pure minimizer. More generally the distance conclusion holds for a continuous, jointly convex state metric. The concrete $A,B,C$ conclusions use root-fidelity concavity and decreasing transforms; they do not assume the source's false joint-convexity claim.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 8, Section IV C: pure inputs suffice for worst-case optimization

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

/-- Section IV C, PDF p.8: all four concrete maxima and minimum squared fidelity are attained
at pure inputs and bound every mixed input. This avoids the false double-convexity premise. -/
theorem pureMixed (E F : FiniteProcess I I) :
    (∀ c : Choice, ∃ psi : ProcessPureInput I,
      maxDistance (stateDistance c) E.val F.val =
        stateDistance c (E.val (pureDensity psi.val)) (F.val (pureDensity psi.val)) ∧
      ∀ rho : ProcessDensityInput I, stateDistance c (E.val rho.val) (F.val rho.val) ≤
        stateDistance c (E.val (pureDensity psi.val)) (F.val (pureDensity psi.val))) ∧
    (∃ psi : ProcessPureInput I, minFidelity E.val F.val =
      fidelity (E.val (pureDensity psi.val)) (F.val (pureDensity psi.val)) ∧
      ∀ rho : ProcessDensityInput I, fidelity (E.val (pureDensity psi.val)) (F.val (pureDensity psi.val)) ≤
        fidelity (E.val rho.val) (F.val rho.val)) ∧
    (∀ delta : FiniteStateDistance, StateMetrics delta → StateContinuous delta →
      StateDoublyConvex delta → ∃ psi : ProcessPureInput I,
        maxDistance delta E.val F.val = delta (E.val (pureDensity psi.val))
          (F.val (pureDensity psi.val)) ∧
        ∀ rho : ProcessDensityInput I, delta (E.val rho.val) (F.val rho.val) ≤
          delta (E.val (pureDensity psi.val)) (F.val (pureDensity psi.val))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
