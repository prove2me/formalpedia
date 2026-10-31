-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P12_rotor_exact_correction
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P12.rotor_exact_correction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:45:50.674069+00:00
-- url     : https://prove2.me/theorems/c189340e-1c04-41d6-80c4-839b635f0210
-- title:
--   §IV (19)–(20): rotor code
-- statement:
--   Let $n,r$ be positive integers and $m=nr$. Represent rotor distributions by their integer-angular-momentum Fourier coefficients. The explicit encoder has coefficients $n^{-1/2}\mathbf1_{r\mid L}\sum_j c_j e^{-2\pi iLj/m}$. It is injective and its image is exactly the common $+1$ eigenspace of multiplication by $e^{im\theta}$ and rotation by $2\pi n/m$. Its coefficient sequences are bounded; they are not asserted to be in $\ell^2(\mathbb Z)$. The logical rotation by $2\pi/m$ is $X$, and multiplication by $e^{ir\theta}$ is $Z$. One algebraic syndrome decoder separates all errors in the strict window
--
--   $$|\Delta\theta|<\frac\pi m,\qquad |\Delta L|<\frac r2=\frac m{2n},\quad\Delta L\in\mathbb Z.$$
--
--   Angles use the central representative of their circular displacement. The common linear decoder also preserves finite coherent sums of these ideal errors.
-- source:
--   Encoding a qubit in an oscillator, arXiv:quant-ph/0008040v3, PDF p. 4, §IV (19)–(20): rotor code

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P12

noncomputable section

open scoped BigOperators

open MeasureTheory Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

namespace QAlgorithms.Papers.Independent.Intakenext100.P12

/-- Section IV (19)–(20), PDF p.4: the rotor code, its logical operations and a common
ideal syndrome decoder. The missing absolute-value bars in the angular prose are read as
shift magnitude, consistently with the preceding finite correction argument. -/
theorem rotor_exact_correction (n r : ℕ) (hn : 0 < n) (hr : 0 < r) :
    Function.Injective (rotorEncode n r) ∧
    (∀ psi : ℤ → ℂ, IsRotorStabilized n r psi ↔ ∃ c, rotorEncode n r c = psi) ∧
    (∀ c : Fin n → ℂ, ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℤ, ‖rotorEncode n r c L‖ ≤ C) ∧
    (∀ c : Fin n → ℂ,
      rotorError (2 * Real.pi / (n * r)) 0 (rotorEncode n r c) =
        rotorEncode n r (logicalCycle n c) ∧
      rotorError 0 r (rotorEncode n r c) = rotorEncode n r (logicalClock n c)) ∧
    (∃ R : (ℤ → ℂ) →ₗ[ℂ] ({e // e ∈ rotorCell n r} → Fin n → ℂ),
      ∀ (e : {e // e ∈ rotorCell n r}) (c : Fin n → ℂ),
        R (rotorError e.val.1 e.val.2 (rotorEncode n r c)) = fun s => if s = e then c else 0) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P12

end
