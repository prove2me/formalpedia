-- Prove2me | Theorems.Thm_QuantumLinSys_Fourier_bound_p13
-- name    : QuantumLinSys.Fourier.bound_p13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:19:08.745405+00:00
-- url     : https://prove2.me/theorems/abee1125-51ba-4502-a1ab-d38146aea6f8
-- title:
--   Proof of Lemma 11, p. 13 — reciprocal-exponential bound
-- statement:
--   For each real $x\in[-1,1]$ with $x\ne0$,
--   $$
--   \left|\frac1{1-e^{-ix}}-\frac1{ix}\right|<1.
--   $$
--
--   The bound controls the error caused by replacing an integral in the $y$ variable with a finite geometric sum.
--
--   **Formalization Note** The printed phrase “for all $x\in[-1,1]$” presupposes the reciprocals are defined. Lean explicitly excludes $x=0$, where totalized division would give a meaningless instance of the inequality.
-- source:
--   Childs, Kothari and Somma, Quantum algorithm for systems of linear equations with exponentially improved dependence on precision, arXiv:1511.02306v2, proof of Lemma 11, p. 13, inline bound beginning 'Since |1/(1−e^{−ix}) − 1/(ix)| < 1'

import Mathlib
import Definitions.Def_QuantumLinSys_Fourier_Setting

namespace QuantumLinSys.Fourier

/-- The inline reciprocal-exponential bound in the proof of Lemma 11, p. 13. -/
theorem bound_p13 (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    ‖1 / (1 - Complex.exp (-Complex.I * x)) -
      1 / (Complex.I * x)‖ < 1 := by sorry

end QuantumLinSys.Fourier
