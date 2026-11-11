-- Prove2me | Theorems.Thm_SwitchingStable_Universal_lemma_17
-- name    : SwitchingStable.Universal.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:58:24.389374+00:00
-- url     : https://prove2.me/theorems/2573df8f-c820-4983-8f2f-234b447f8506
-- title:
--   Lemma 17 — Witness transport and changed-edge allocation
-- statement:
--   Fix a direction in the promoted market and sum over all occurrences. Cuts and nonnegative event contributions admit an allocation beyond $L_0$ of total expected value at least
--   $$(\gamma+\delta_4)(e-e_{\rm adj}-b_E)+(\delta_4+\delta_5)(w-b_W)+\gamma t_0-(\gamma+\delta_4+\delta_5)b_3.$$
--   A nonfailing tail and its eligible one- and two-swap predecessors retain layers $\{1,2,3\}$, $\{2,3,4\}$, $\{3,4,5\}$ unless an edge supplying a witness changed. Second-boundary changed groups keep depth one and reserve $3(\xi+\psi)$; the disjoint third-boundary changed groups keep depth two and reserve $3\psi$. There is at most one predecessor of each kind.
--
--   Actual selected terms, paid contributions and reserves are pointwise dominated by actual saving. The statement includes the proof's missing-layer counts $m_1=b_C+b_E+b_W+f_a+2z_1+z_{1,W}$ and $m_2\le c+f_a+b_E+b_W+3b_3+3z_1+3z_2$. These are counts of the stated depth assignment, and $z_{1,W}\le z_1$.
--
--   Differences from the source:
--   - encoding: Cuts and event contributions can be allocated, with reserves beyond all allocated costs → An existential allocation of nonnegative integrable random functions dominated by actual saving, with explicit fixed-order suppliers, depths, and missing-layer counts; reason: Exposes the no-reuse and residual requirements and the displayed proof counts on printed page 11; no desired saving inequality is an input axiom.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 10, PDF p. 11, Lemma 17

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Local

namespace SwitchingStable.Universal

open MeasureTheory

theorem lemma_17 {n : ℕ} (I : StableMatching.Instance n) (hI : StablePartnersFirst I) (ε : Direction) :
    (∀ o : Occurrence I,
      legalCuts I o.1.val o.2 ε (allocatedCuts I o.1.val ε o.2) ∧
      (∀ c ∈ selectedCuts I o.1.val ε o.2, Elementary I o.1.val o.2 ε c) ∧
      Set.InjOn Cut.layer (selectedCuts I o.1.val ε o.2 : Set (Cut n))) ∧
    (∀ (ν : StableMatching.Matching n) (u : Fin n), I.IsStable ν → T0 I ν ε u →
      (∀ μ1 μ2 : StableMatching.Matching n, I.IsStable μ1 → I.IsStable μ2 →
        E I μ1 ε u → ¬ Eadj I μ1 ε u → E I μ2 ε u → ¬ Eadj I μ2 ε u →
        swap I μ1 ε u = ν → swap I μ2 ε u = ν → μ1=μ2) ∧
      (∀ μ1 μ2 : StableMatching.Matching n, I.IsStable μ1 → I.IsStable μ2 →
        W I μ1 ε u → W I μ2 ε u → swapTwice I μ1 ε u = ν → swapTwice I μ2 ε u = ν → μ1=μ2)) ∧
    ∃ paid reserve : Occurrence I → Sample n → ℝ,
      IsAllocation I ε paid reserve ∧
      (occurrenceCounts I ε).L0 + (occurrenceCounts I ε).extra ≤
        ∑ o : Occurrence I, (selectedCost I o.1.val ε o.2 + expected (paid o)) ∧
      (∀ o : Occurrence I,
        (ChangedSecond I o.1.val ε o.2 → 3*(xi+psi) ≤ expected (reserve o)) ∧
        (ChangedThird I o.1.val ε o.2 → 3*psi ≤ expected (reserve o)) ∧
        (¬ ChangedSecond I o.1.val ε o.2 → ¬ ChangedThird I o.1.val ε o.2 → reserve o = 0)) ∧
      (let v := occurrenceCounts I ε
       let z1 : ℝ := count I (fun μ u => ChangedSecond I μ ε u)
       let z2 : ℝ := count I (fun μ u => ChangedThird I μ ε u)
       let z1W : ℝ := count I (fun μ u => ChangedSecond I μ ε u ∧ HasW I μ ε u)
       z1W ≤ z1 ∧
       (missingCount I ε 2 : ℝ) = v.bC+v.bE+v.bW+v.fa+2*z1+z1W ∧
       (missingCount I ε 3 : ℝ) ≤ v.c+v.fa+v.bE+v.bW+3*v.b3+3*z1+3*z2) := by sorry

end SwitchingStable.Universal
