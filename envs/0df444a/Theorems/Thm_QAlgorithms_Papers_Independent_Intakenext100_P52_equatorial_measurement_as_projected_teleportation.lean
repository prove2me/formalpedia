-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_equatorial_measurement_as_projected_teleportation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.equatorial_measurement_as_projected_teleportation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:48:09.331997+00:00
-- url     : https://prove2.me/theorems/d1d7991a-661a-4fbf-b522-3830fd1f8f6a
-- title:
--   §7.1: equatorial measurement as projected teleportation
-- statement:
--   For real $\theta$, define $W(\theta)=H\operatorname{diag}(1,e^{i\theta})$, $|H\rangle=CZ|++\rangle$, and $|a_j\rangle=(W(-\theta)^\dagger\sigma_j\otimes I)|H\rangle$, with $\sigma_j=I,X,Z,XZ$. These four kets are orthonormal and equal
--
--   $$ |a_{0,1}\rangle=\frac{|00\rangle\pm e^{i\theta}|11\rangle}{\sqrt2},\qquad |a_{2,3}\rangle=\frac{|01\rangle\pm e^{i\theta}|10\rangle}{\sqrt2}. $$
--
--   Let $F=|0\rangle\langle00|+|1\rangle\langle11|$ and $|m_s\rangle=(|0\rangle+(-1)^s e^{i\theta}|1\rangle)/\sqrt2$. Then $F^\dagger|m_s\rangle\langle m_s|F=|a_s\rangle\langle a_s|$ for $s=0,1$, while $F|a_j\rangle\langle a_j|F^\dagger=0$ for $j=2,3$. This is the exact two-outcome conditional measurement identity on the projected site, rather than a method for deterministic postselection.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, PDF p. 17, §7.1: equatorial measurement as projected teleportation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Projected teleportation, PDF pp.17–18: all four kets and their even/odd
placement, and the exact pullback of the two normalized equatorial effects.
Odd alternatives vanish upon projection; this is a conditional identity, not
a deterministic postselection procedure for an arbitrary teleportation. -/
theorem equatorial_measurement_as_projected_teleportation (theta : ℝ) :
    (∀ a : Fin 4, cutDownKet theta a = cutDownFormula theta a) ∧
    Orthonormal ℂ (cutDownKet theta) ∧
    (∀ p : QubitPair, p.1 ≠ p.2 → cutDownKet theta 0 p = 0 ∧ cutDownKet theta 1 p = 0) ∧
    (∀ p : QubitPair, p.1 = p.2 → cutDownKet theta 2 p = 0 ∧ cutDownKet theta 3 p = 0) ∧
    (∀ s : Bool, fuseᴴ * pureDensity (equatorial theta s) * fuse =
      pureDensity (cutDownKet theta (if s then 1 else 0))) ∧
    fuse * pureDensity (cutDownKet theta 2) * fuseᴴ = 0 ∧
    fuse * pureDensity (cutDownKet theta 3) * fuseᴴ = 0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P52

end
