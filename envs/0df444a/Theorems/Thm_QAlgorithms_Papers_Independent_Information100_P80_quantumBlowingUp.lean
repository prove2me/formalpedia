-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P80_quantumBlowingUp
-- name    : QAlgorithms.Papers.Independent.Information100.P80.quantumBlowingUp
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:17:14.560644+00:00
-- url     : https://prove2.me/theorems/4c6fa7c1-f445-4e06-9614-371594781f05
-- title:
--   Theorem 2 (Quantum blowing-up lemma)
-- statement:
--   Let $\mathcal N:A\to B$ be a finite-dimensional CPTP channel with a chosen Stinespring isometry $U:A\to B\otimes E$, so $U^\dagger U=I_A$ and $\mathcal N(X)=\operatorname{tr}_E(UXU^\dagger)$. Write $\Pi=UU^\dagger$. Let an entanglement-transmission code have positive integer dimension $M$ and actual squared entanglement fidelity $F>0$. Its encoder and decoder are arbitrary CPTP maps, and the reference is untouched. Fix $0<\varepsilon<1$ and $\Gamma>0$. Suppose an arbitrary operator $\widetilde\Pi$ satisfies
--   $$
--   \widetilde\Pi\Pi=\Pi\widetilde\Pi=\Pi,\qquad
--   \|\widetilde\Pi\|_\pi\le\Gamma,\qquad
--   \|\widetilde\Pi-\Pi\|_\infty\le\frac{\varepsilon\sqrt F}{2}.
--   $$
--
--   The projective norm uses the $B:E$ bipartition and local spectral norms. There exists an entanglement-transmission code for the same channel, of positive integer dimension $M'$ and squared fidelity $F'$, with
--   $$
--   F'\ge1-\varepsilon^2,\qquad
--   \log_2 M'\ge\log_2 M+\log_2 F-2\log_2\Gamma-4\log_2(2/\varepsilon)-1.
--   $$
--
--   This amplifies fidelity while bounding the loss in logarithmic message size. The approximant need not be positive, Hermitian or a projector, and a negative dimension lower bound is allowed: a dimension-one code suffices in that regime.
-- source:
--   Strong Converses for Quantum Channel Capacities from Blowing-Up Lemmata, arXiv:2609.11771v1, PDF p. 7, Theorem 2 (Quantum blowing-up lemma)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P80

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

/-- Theorem 2, PDF p.7, (21)–(22); dimension-one fallback on p.8.
The approximant is an arbitrary operator; the output is a transmission code. -/
theorem quantumBlowingUp
    {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    [Nonempty A] [Nonempty B] [Nonempty E]
    (N : Superop A B) (hN : IsChannel N) (U : Matrix (B × E) A ℂ)
    (hU : Uᴴ * U = 1)
    (hdilation : ∀ X, N X = traceRight (U * X * Uᴴ))
    (C : TransmissionCode A B) (hF : 0 < transmissionFidelity N C)
    (epsilon Gamma : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (hG : 0 < Gamma)
    (Ptilde : Matrix (B × E) (B × E) ℂ)
    (hleft : Ptilde * (U * Uᴴ) = U * Uᴴ)
    (hright : (U * Uᴴ) * Ptilde = U * Uᴴ)
    (hprojective : projectiveNorm Ptilde ≤ Gamma)
    (haccuracy : specNorm (Ptilde - U * Uᴴ) ≤
      epsilon * Real.sqrt (transmissionFidelity N C) / 2) :
    ∃ Cnew : TransmissionCode A B,
      1 - epsilon ^ 2 ≤ transmissionFidelity N Cnew ∧
      log2 (C.M : ℝ) + log2 (transmissionFidelity N C) - 2 * log2 Gamma -
        4 * log2 (2 / epsilon) - 1 ≤ log2 (Cnew.M : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Information100.P80

end
