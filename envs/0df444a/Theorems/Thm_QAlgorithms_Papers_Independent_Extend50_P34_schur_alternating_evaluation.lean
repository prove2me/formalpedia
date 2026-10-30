-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_schur_alternating_evaluation
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.schur_alternating_evaluation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:05:36.667642+00:00
-- url     : https://prove2.me/theorems/1fbccd49-1a89-4b94-bd3e-cd11705e995d
-- title:
--   Theorem 4.18
-- statement:
--   Let $\mu\vdash k$ and let $d$ be even. Then
--
--   $$s_\mu(1,-1,\ldots,1,-1)=\begin{cases}0,&\mu\text{ not balanced},\chi_\mu(2^{k/2})\,d^{\uparrow[\mu]_{\rm even}}/k!!,&\mu\text{ balanced}.\end{cases}$$
--
--   Balanced partitions have even size, and $0!!=1$. The Schur polynomial uses its unrestricted zero extension, so no height restriction is imposed. This gives the exact alternating specialization used in mixedness lower bounds.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 42, Theorem 4.18

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Theorem 4.18, arXiv:1501.05028v1, PDF p.42. Balanced branch implies even k; class evaluation uses k/2 twocycles only on that branch. At mu=(2),d=2 the value is +1; at mu=(1,1) it is -1. -/
theorem schur_alternating_evaluation
    (mu : YoungDiagram) (d : ℕ) (heven : Even d) :
    schurAt mu (fun i : Fin d => if Even i.val then 1 else -1) =
      if DominoBalanced mu then
        classCharacter mu (Multiset.replicate (mu.card/2) 2) /
          evenDoubleFactorial mu.card * parityProduct d mu true
      else 0 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
