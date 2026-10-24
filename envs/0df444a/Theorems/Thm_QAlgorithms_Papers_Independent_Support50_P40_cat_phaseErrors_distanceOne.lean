-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P40_cat_phaseErrors_distanceOne
-- name    : QAlgorithms.Papers.Independent.Support50.P40.cat_phaseErrors_distanceOne
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:08:21.784912+00:00
-- url     : https://prove2.me/theorems/9e67bc83-15a1-4c9c-9eed-deb82c51a86a
-- title:
--   Cat phase errors have identical restrictions; distance is one
-- statement:
--   Let $p=m+1\ge1$ and let $C_p=\operatorname{span}\{|0\rangle^{\otimes p},|1\rangle^{\otimes p}\}$. For a physical wire $a$, write $Z_a$ for Pauli $Z$ on that wire and identity elsewhere.
--
--   The code has dimension two and distance exactly one. Its phase-error restrictions satisfy
--
--   $$
--   Z_a\psi=Z_b\psi\quad(a,b\in\{1,\ldots,p\},\ \psi\in C_p),\qquad
--   Z_aZ_b\psi=\psi\quad(a\ne b,\ \psi\in C_p).
--   $$
--
--   These are identities of operators restricted to the entire code, so they apply to every normalized code state. At $p=1$ the distinct-wire pair claim is vacuous, while the distance claim remains meaningful. No formal claim of degeneracy for correction radius zero is made.
--
--   **Formalization Note** Page 20 prints “pairs of amplitude errors.” The statement corrects this to phase errors, as forced by Eqs. (31)–(33). For example $X_1X_2|000\rangle$ leaves the three-qubit cat subspace, whereas $Z_1Z_2$ fixes it. Independent moderation of the correction is required.
-- source:
--   Quantum Channel Capacity of Very Noisy Channels, arXiv:quant-ph/9706061v3, PDF p. 20, Section VI: indistinguishable cat phase errors and distance one, corrected

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P40

namespace QAlgorithms.Papers.Independent.Support50.P40

open QAlgorithms QAlgorithms.Stabilizer

open scoped ComplexConjugate Matrix

noncomputable section

/-- PDF pp.16,20, Eqs.(31)--(33): corrected phase-error degeneracy and
exact distance one. Printed: "all pairs of amplitude errors". Changed to
pairs of PHASE errors: Z_a Z_b stabilizes the displayed code; X_a X_b
does not (p=3), and at p=2 it is logical X. This source correction requires
independent moderation. It does not claim degeneracy at t=floor(d/2)=0. -/
theorem cat_phaseErrors_distanceOne (m : ℕ) :
    Module.finrank ℂ (catSpace m) = 2 ∧ HasDistance (catSpace m) 1 ∧
    (∀ (a b : Fin (m + 1)) (psi : EuclideanSpace ℂ (Qubits (m + 1))),
      psi ∈ catSpace m → act (singleZ a) psi = act (singleZ b) psi) ∧
    (∀ (a b : Fin (m + 1)), a ≠ b →
      ∀ psi : EuclideanSpace ℂ (Qubits (m + 1)), psi ∈ catSpace m →
        act (singleZ a * singleZ b) psi = psi) := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P40
