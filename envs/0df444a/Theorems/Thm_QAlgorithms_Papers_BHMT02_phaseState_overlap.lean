-- Prove2me | Theorems.Thm_QAlgorithms_Papers_BHMT02_phaseState_overlap
-- name    : QAlgorithms.Papers.BHMT02.phaseState_overlap
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T18:41:54.33627+00:00
-- url     : https://prove2.me/theorems/ca1afa85-e093-464a-8eb3-40155254e56d
-- title:
--   BHMT Lemma 10: overlap of two Fourier phase states
-- statement:
--   This is the overlap identity for Fourier phase states (Brassard, Høyer, Mosca, Tapp, Lemma 10), which yields the outcome distribution of Fourier-transform phase estimation.
--
--   Let $M > 0$ be an integer. For a real number $0 \le \omega < 1$, the phase state on the $M$-dimensional register with orthonormal basis $|0\rangle, \dots, |M-1\rangle$ is
--
--   $$|S_M(\omega)\rangle = \frac{1}{\sqrt M} \sum_{y=0}^{M-1} e^{2\pi i \omega y} |y\rangle .$$
--
--   For reals $\omega_0, \omega_1$, let $d(\omega_0, \omega_1) = \min_{z \in \mathbb Z} |z + \omega_1 - \omega_0|$ be the distance on the circle $\mathbb R / \mathbb Z$. Let $0 \le \omega_0 < 1$, $0 \le \omega_1 < 1$, and $\Delta = d(\omega_0, \omega_1)$. Then:
--
--   1. if $\Delta = 0$, then $|\langle S_M(\omega_0) | S_M(\omega_1)\rangle|^2 = 1$;
--   2. if $\Delta \ne 0$, then
--
--   $$|\langle S_M(\omega_0) | S_M(\omega_1)\rangle|^2 = \frac{\sin^2(M \Delta \pi)}{M^2 \sin^2(\Delta \pi)} .$$
--
--   The inner product is conjugate-linear in its first argument. Taking $\omega_0 = x/M$ gives the probability of outcome $x$ when $F_M^{-1}|S_M(\omega_1)\rangle$ is measured, which is the paper's Theorem 11 and the lecture notes' Proposition 3.11.
--
--   **Formalization Note** The phase state is the shared definition `bhmtPhaseState M ω` on `EuclideanSpace ℂ (Fin M)`, and $d$ is `circDist ω0 ω1 = |(ω0 − ω1) − round(ω0 − ω1)|`, which equals the minimum in Definition 9.
-- source:
--   Quantum Amplitude Amplification and Estimation (Brassard, Høyer, Mosca, Tapp), arXiv:quant-ph/0005055v1, Lemma 10, PDF p. 16. https://arxiv.org/abs/quant-ph/0005055v1 . PDF SHA-256: badedce80b0fe53e6cd93f915ce79c9680e375bb6565f83d2f572bc4114b0278.

import Definitions.Def_QAlgorithms_Defs_PhaseOracles
set_option autoImplicit false

namespace QAlgorithms.Papers.BHMT02

/-- BHMT p.16, Lemma 10: for `0 ≤ ω0, ω1 < 1` and `∆ = d(ω0, ω1)`, if `∆ = 0` then
`|⟨S_M(ω0)|S_M(ω1)⟩|² = 1`, and otherwise
`|⟨S_M(ω0)|S_M(ω1)⟩|² = sin²(M∆π) / (M² sin²(∆π))`. The integer `M > 0` is the standing
assumption of Definition 8. -/
theorem phaseState_overlap (M : ℕ) (hM : 0 < M) (ω0 ω1 : ℝ) (h0 : 0 ≤ ω0) (h0' : ω0 < 1)
    (h1 : 0 ≤ ω1) (h1' : ω1 < 1) :
    (circDist ω0 ω1 = 0 →
      ‖inner ℂ (bhmtPhaseState M ω0) (bhmtPhaseState M ω1)‖ ^ 2 = 1) ∧
    (circDist ω0 ω1 ≠ 0 →
      ‖inner ℂ (bhmtPhaseState M ω0) (bhmtPhaseState M ω1)‖ ^ 2 =
        Real.sin ((M : ℝ) * circDist ω0 ω1 * Real.pi) ^ 2 /
          ((M : ℝ) ^ 2 * Real.sin (circDist ω0 ω1 * Real.pi) ^ 2)) := by
  sorry

end QAlgorithms.Papers.BHMT02
