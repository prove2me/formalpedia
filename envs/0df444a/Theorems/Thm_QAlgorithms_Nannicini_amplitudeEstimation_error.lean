-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_amplitudeEstimation_error
-- name    : QAlgorithms.Nannicini.amplitudeEstimation_error
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:44:37.302209+00:00
-- url     : https://prove2.me/theorems/74ab749b-b1f2-4c9e-8850-a213b6c3d301
-- title:
--   Error bound of amplitude estimation with m qubits
-- statement:
--   This is the accuracy guarantee of amplitude estimation.
--
--   Let $S$ be a unitary on $n$ qubits and let $|\psi_G\rangle, |\psi_B\rangle$ be orthogonal unit vectors with $S|\vec 0\rangle_n = \sin\theta\,|\psi_G\rangle + \cos\theta\,|\psi_B\rangle$, $\theta \in [0, \tfrac{\pi}{2}]$. Let $R$ be a unitary with $R|\psi_G\rangle = -|\psi_G\rangle$, $R|\psi_B\rangle = |\psi_B\rangle$, and let $G = S F S^\dagger R$ with $F = 2|\vec 0\rangle\langle \vec 0| - I$.
--
--   The amplitude estimation algorithm with $m$ qubits prepares $|\vec 0\rangle_m \otimes S|\vec 0\rangle_n$, runs phase estimation of $G$ (Hadamards, controlled $G^{2^k}$, inverse QFT $Q_m^\dagger$) on the first register, measures it to obtain $\vec b \in \{0,1\}^m$, and returns $\tilde\theta = \pi(1 - 0.\vec b)$ if $b_1 = 1$ and $\tilde\theta = \pi\, 0.\vec b$ otherwise. With $a = \sin^2\theta$ and $\tilde a = \sin^2\tilde\theta$,
--   $$\Pr\left[\,|a - \tilde a| \le \frac{2\pi\sqrt{a(1-a)}}{2^m} + \frac{\pi^2}{2^{2m}}\,\right] \ge \frac{8}{\pi^2}.$$
--
--   The error decreases like $2^{-m}$, i.e. linearly in the number of applications of $G$, which is the source of the quadratic speedup over classical sampling.
--
--   **Formalization Note** The final pre-measurement state is the frozen `aeState m S R` and $\tilde\theta$ is the frozen `aeAngle b`; the probability is that of the event on the first register.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 88, Proposition 4.21. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
set_option autoImplicit false

namespace QAlgorithms.Nannicini



/-- Nannicini p.88, Proposition 4.21 (Thm. 12 in Brassard et al. 2002): in the setting of §4.3
(p.83: `S` an `n`-qubit unitary, `S|0⟩ = sin θ |ψ_G⟩ + cos θ |ψ_B⟩` with `ψ_G`, `ψ_B` orthogonal
states and `θ ∈ [0, π/2]`; `R` a unitary with `R|ψ_G⟩ = −|ψ_G⟩`, `R|ψ_B⟩ = |ψ_B⟩`), apply the
amplitude estimation algorithm of §4.3.3 (p.86, Fig. 4.9) with `m` qubits for phase estimation:
prepare `|0⟩_m ⊗ S|0⟩_n`, run phase estimation of `G = S F S† R`, measure the first register to
get `b`, and return `θ̃ = π(1 − 0.b)` if `b_1 = 1`, `θ̃ = π·0.b` otherwise. With `a = sin²θ` and
`ã = sin²θ̃`, the outcome satisfies `|a − ã| ≤ 2π√(a(1 − a))/2^m + π²/2^{2m}` (4.8) with
probability at least `8/π²`. -/
theorem amplitudeEstimation_error {n : ℕ} (m : ℕ) (S R : Matrix (Qubits n) (Qubits n) ℂ)
    (psiG psiB : EuclideanSpace ℂ (Qubits n)) (θ : ℝ)
    (hS : S ∈ Matrix.unitaryGroup (Qubits n) ℂ) (hR : R ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (hG : IsState psiG) (hB : IsState psiB) (horth : inner ℂ psiG psiB = 0)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2)
    (hprep : act S (zeroKet n) = (Real.sin θ : ℂ) • psiG + (Real.cos θ : ℂ) • psiB)
    (hRG : act R psiG = -psiG) (hRB : act R psiB = psiB) :
    8 / Real.pi ^ 2 ≤ probEvent (aeState m S R) fun z =>
      |Real.sin θ ^ 2 - Real.sin (aeAngle z.1) ^ 2| ≤
        2 * Real.pi * Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2)) / (2 : ℝ) ^ m +
          Real.pi ^ 2 / (2 : ℝ) ^ (2 * m) := by
  sorry


end QAlgorithms.Nannicini
