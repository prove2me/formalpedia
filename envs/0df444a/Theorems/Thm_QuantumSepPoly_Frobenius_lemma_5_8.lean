-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_lemma_5_8
-- name    : QuantumSepPoly.Frobenius.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:23.603084+00:00
-- url     : https://prove2.me/theorems/5621451d-1209-431e-9afa-5d9bf8804f50
-- title:
--   Lemma 5.8 — Inexact Frank-Wolfe recurrence
-- statement:
--   Let $\rho$ be Hermitian with $\|\rho\|_F\le1$, $0<\eta\le1$, $\tau=\eta^2/64$, $T=\lceil256/\eta^2\rceil$, and $T3^{-\ell}\le1/3$. Consider the actual amplified calls of a finite program on the adaptive residuals of the source update, on the simultaneous good-output event. With
--   $$f_\rho(\sigma)=\tfrac12\|\sigma-\rho\|_F^2-\min_{\psi\in\operatorname{Sep}}\tfrac12\|\psi-\rho\|_F^2,$$
--   for each source index $1\le t\le T-1$,
--   $$f_\rho(\sigma_{t+1})-2\tau\le(1-2/(t+2))(f_\rho(\sigma_t)-2\tau)+2(2/(t+2))^2.$$
--   This is a pathwise recurrence on the computed process, not a guarantee assumed by the main goal. Adaptive success events are not assumed independent.
--
--   Differences from the source:
--   - encoding: coordinates labelled 1 through d → coordinates indexed by Fin d from 0 through d-1; reason: canonical relabelling preserves all vectors, matrices, sums, and constraints
--   - encoding: source iterates sigma_1 through sigma_T with T=256/eta^2 → zero-based iterate counter, T rounded upward, and frozen state after early acceptance; reason: the coefficient 2/(t+3) is exactly 2/(source_t+2); rounding and freezing preserve every executed update
--   - generalization: the particular optimization subroutine from Theorem 5.7 on its good event → any finite RAM subroutine conditioned on its actual amplified outputs satisfying that event; reason: the source subroutine is an instance and no such guarantee is assumed by the mission goal
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Lemma 5.8, p. 23 (PDF p. 23); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_FrankWolfe

namespace QuantumSepPoly.Frobenius

/-- Lemma 5.8, p.23. Index t=0 encodes the source's first iterate sigma_1.
The event is about actual independently amplified calls on adaptive residuals. -/
theorem lemma_5_8 (d : ℕ) (hd : 0 < d) (ρ : Bip d) (hρ : ρ.IsHermitian) (hnorm : frob ρ ≤ 1)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (P : RAMProgram) (ell : ℕ)
    (hell : (fwIterations η : ℝ) * (3:ℝ)^(-(ell : ℤ)) ≤ 1/3)
    (tapes : ℕ → ℕ → RandomTape) (hgood : fwGoodEvent P η ρ ell tapes)
    (t : ℕ) (ht : t+1 < fwIterations η) :
    potential ρ (fwState P η ρ ell tapes (t+1)) - 2*fwAccuracy η ≤
      (1 - 2/((t:ℝ)+3)) * (potential ρ (fwState P η ρ ell tapes t) - 2*fwAccuracy η) +
        2*(2/((t:ℝ)+3))^2 := by sorry

end QuantumSepPoly.Frobenius
