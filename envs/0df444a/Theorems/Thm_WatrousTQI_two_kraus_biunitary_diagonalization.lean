-- Prove2me | Theorems.Thm_WatrousTQI_two_kraus_biunitary_diagonalization
-- name    : WatrousTQI.two_kraus_biunitary_diagonalization
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-11T22:57:12.942127+00:00
-- url     : https://prove2.me/theorems/ee567a0b-5541-428e-a57a-c8bc914a2708
-- title:
--   Lemma 4.22 — simultaneous biunitary diagonalization
-- statement:
--   Let $d>0$ and let $A_0,A_1$ be arbitrary complex $d\times d$ matrices satisfying both $A_0^\dagger A_0+A_1^\dagger A_1=I_d$ and $A_0A_0^\dagger+A_1A_1^\dagger=I_d$. There exist unitary matrices $U,V$ for which $VA_0U^\dagger$ and $VA_1U^\dagger$ are both diagonal. The same pair $U,V$ works for both matrices. No Hermiticity, invertibility, or linear-independence hypothesis is imposed on $A_0,A_1$.
-- source:
--   John Watrous, The Theory of Quantum Information, Cambridge University Press, 2018, Chapter 4. https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf; Lemma 4.22, equation (4.149), printed pp.225–226 (PDF pp.233–234).

import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate BigOperators

namespace WatrousTQI

theorem two_kraus_biunitary_diagonalization (d : ℕ) (hd : 0 < d)
    (A₀ A₁ : Matrix (Fin d) (Fin d) ℂ)
    (hTP : A₀ᴴ * A₀ + A₁ᴴ * A₁ = 1)
    (hU : A₀ * A₀ᴴ + A₁ * A₁ᴴ = 1) :
    ∃ U V : Matrix.unitaryGroup (Fin d) ℂ,
      ∃ x y : Fin d → ℂ,
        (V : Matrix (Fin d) (Fin d) ℂ) * A₀ *
          (U : Matrix (Fin d) (Fin d) ℂ)ᴴ = Matrix.diagonal x ∧
        (V : Matrix (Fin d) (Fin d) ℂ) * A₁ *
          (U : Matrix (Fin d) (Fin d) ℂ)ᴴ = Matrix.diagonal y := by sorry

end WatrousTQI
