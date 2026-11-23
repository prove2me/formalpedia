-- Prove2me | Theorems.Thm_TIESharp_bsSlotLaw_scaling
-- name    : TIESharp.bsSlotLaw_scaling
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T04:01:26.376574+00:00
-- url     : https://prove2.me/theorems/20e1ea78-8021-463e-aeec-3aae722b416d
-- title:
--   Homogeneity of the slot law, optimum, and makespan in seven machines
-- statement:
--   Let $c>0$, let $t'=t/c$, and let $y$ be a law on assignments on seven machines. Then
--   $$\operatorname{IsBSSlotLaw}(t',y)\Longleftrightarrow\operatorname{IsBSSlotLaw}(t,y),$$
--   $$\mathrm{OPT}(t')=\mathrm{OPT}(t)/c,\qquad C_{\max}(t',A)=C_{\max}(t,A)/c$$
--   for every assignment $A$. In particular, a positive optimum can be normalized to one without changing the assignment distribution.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134, Proposition 5.5 proof, opening normalization on p.27 (homogeneity of the inverse-square/Bounded-Square rule from §2, p.4 and §3.2, p.10).

import Mathlib
import Definitions.Def_TIESharp_opt
import Definitions.Def_TIESharp_IsBSSlotLaw

set_option autoImplicit false

/-- Dividing all processing times by a positive constant preserves a Bounded-Square slot law
and divides the optimum and every assignment's makespan by the same constant. This is the
normalization step at the start of the seven-machine proof. -/
theorem TIESharp.bsSlotLaw_scaling (m : ℕ) (t : Fin 7 → Fin m → ℝ) (c : ℝ) (hc : 0 < c)
    (y : (Fin m → Fin 7) → ℝ) :
    (TIESharp.IsBSSlotLaw (fun i j => t i j / c) y ↔ TIESharp.IsBSSlotLaw t y) ∧
    TIESharp.opt (fun i j => t i j / c) = TIESharp.opt t / c ∧
    ∀ A : Fin m → Fin 7,
      MatousekLP.Scheduling.makespan (Matrix.of (fun i j => t i j / c)) A =
        MatousekLP.Scheduling.makespan (Matrix.of t) A / c := by sorry
