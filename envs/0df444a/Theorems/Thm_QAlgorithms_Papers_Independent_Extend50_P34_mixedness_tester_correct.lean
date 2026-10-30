-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_mixedness_tester_correct
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.mixedness_tester_correct
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:58:03.291068+00:00
-- url     : https://prove2.me/theorems/20ffd4fe-11d3-4ea4-a61d-3585fd9c96d8
-- title:
--   Theorem 4.1
-- statement:
--   There is an absolute $C>0$ such that for $d\ge2$, $0<\epsilon\le1/2$, and any integer $n\ge Cd/\epsilon^2$, the Mixedness Tester accepts exactly when
--
--   $$p_2^\sharp(\lambda)\le(1+\epsilon^2/2)\frac{n(n-1)}d,\qquad\lambda\sim\mathrm{SW}_\rho^n.$$
--
--   It accepts the maximally mixed state with probability at least $2/3$ and rejects every state at distance at least $\epsilon$ with probability at least $2/3$. Thus an integer copy count of order $d/\epsilon^2$ suffices.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 33, Theorem 4.1

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Theorem 4.1, arXiv:1501.05028v1, PDF p.33. Use a sufficiently large absolute multiple and integer n. The acceptance inequality is weak, exactly as printed. -/
theorem mixedness_tester_correct
    : ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1/2 →
        ∀ n : ℕ, C*d/epsilon^2 ≤ (n : ℝ) →
          (∀ rho : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix rho →
            (decreasingSpectrum rho = unif d → 2/3 ≤ mixednessStateAccept n epsilon rho) ∧
            (epsilon ≤ tv (decreasingSpectrum rho) (unif d) →
              mixednessStateAccept n epsilon rho ≤ 1/3)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
