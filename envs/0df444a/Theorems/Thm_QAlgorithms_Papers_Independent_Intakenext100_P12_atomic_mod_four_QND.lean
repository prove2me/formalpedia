-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P12_atomic_mod_four_QND
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P12.atomic_mod_four_QND
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:11:59.991666+00:00
-- url     : https://prove2.me/theorems/1f483f3c-c416-4677-ac85-db2f518df274
-- title:
--   §XI.A (109)–(111): atom-assisted nondemolition mod-four measurement
-- statement:
--   Let $\lambda>0$, and let the oscillator have Fock amplitudes $\psi_k$ with $\sum_k|\psi_k|^2=1$ and zero odd-$k$ amplitudes. The atom starts in $(|g\rangle+|e\rangle)/\sqrt2$, with $\sigma_z=-1$ on $g$ and $+1$ on $e$. Evolving under $H'=\lambda N\sigma_z$ for $t=\pi/(4\lambda)$ gives the controlled phases of (111). Measuring the atom in its plus/minus basis has branch amplitudes
--
--   $$K_+\psi=e^{i\pi N/4}\Pi_{N=0\bmod4}\psi,\qquad K_-\psi=e^{i\pi N/4}\Pi_{N=2\bmod4}\psi.$$
--
--   The outcome probabilities are the squared norms of these projections and sum to one. Neither branch mixes sectors, and an immediate repeated measurement cannot give the opposite outcome. The common known number-dependent backaction is retained.
-- source:
--   Encoding a qubit in an oscillator, arXiv:quant-ph/0008040v3, PDF p. 14, §XI.A (109)–(111): atom-assisted nondemolition mod-four measurement

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P12

noncomputable section

open scoped BigOperators

open MeasureTheory Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

namespace QAlgorithms.Papers.Independent.Intakenext100.P12

/-- Section XI.A (109)–(111), PDF pp.14–15: exact atom calculation and repeatable mod-four sectors.
The physical oscillator input has total squared amplitude one and even parity. -/
theorem atomic_mod_four_QND (lambda : ℝ) (hl : 0 < lambda) (psi : ℕ → ℂ)
    (hnorm : HasSum (fun k => ‖psi k‖ ^ 2) 1)
    (heven : ∀ k, k % 2 = 1 → psi k = 0) :
    (∀ k atom, atomEvolution lambda (Real.pi / (4 * lambda))
      (fun ka => psi ka.1 / (Real.sqrt 2 : ℂ)) k atom =
      cisPhase ((if atom then -1 else 1) * Real.pi * k / 4) * psi k / (Real.sqrt 2 : ℂ)) ∧
    (∀ b k, atomBranch b psi k =
      cisPhase (Real.pi * k / 4) * numberSector (if b then 2 else 0) psi k) ∧
    (∀ b k, ‖atomBranch b psi k‖ ^ 2 = ‖numberSector (if b then 2 else 0) psi k‖ ^ 2) ∧
    (∑' k, ‖atomBranch false psi k‖ ^ 2) + (∑' k, ‖atomBranch true psi k‖ ^ 2) = 1 ∧
    (∀ b k, atomBranch (!b) (atomBranch b psi) k = 0) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P12

end
