-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_amplitudeAmplification
-- name    : QAlgorithms.DeWolf.amplitudeAmplification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:42:06.438984+00:00
-- url     : https://prove2.me/theorems/c350f2a0-be59-400a-90c4-f168c0e5ffc3
-- title:
--   Amplitude amplification: Q^k A|0^m⟩ = sin((2k+1)θ)|ψ1⟩ + cos((2k+1)θ)|ψ0⟩, and O(1/√p) rounds suffice
-- statement:
--   Let $A$ be a unitary on $m$ qubits (a circuit without measurements) and $p\in(0,1]$, and suppose
--
--   $$A|0^m\rangle=\sqrt p\,|\psi_1\rangle+\sqrt{1-p}\,|\psi_0\rangle,$$
--
--   where $|\psi_1\rangle,|\psi_0\rangle$ are orthogonal unit vectors (the good and the bad state). Let $R_G$ be a unitary with $R_G|\psi_1\rangle=-|\psi_1\rangle$ and $R_G|\psi_0\rangle=|\psi_0\rangle$, let $R_0$ fix $|0^m\rangle$ and negate every other basis state, and let $Q=AR_0A^{-1}R_G$ be one round (reflect through $|\psi_0\rangle$, then through $|U\rangle=A|0^m\rangle$). Put $\theta=\arcsin\sqrt p$.
--
--   1. For every $k\in\mathbb N$,
--   $$Q^kA|0^m\rangle=\sin((2k+1)\theta)\,|\psi_1\rangle+\cos((2k+1)\theta)\,|\psi_0\rangle.$$
--   2. If $k\in\mathbb N$ is an integer closest to $\frac{\pi}{4\theta}-\frac12$, then $k\le\frac{\pi}{4\theta}\le\frac{\pi}{4\sqrt p}$, and the good state has probability $|\langle\psi_1|Q^kA|0^m\rangle|^2\ge 1-p$.
--
--   So $O(1/\sqrt p)$ applications of $A$, $A^{-1}$ and $R_G$ raise the success probability from $p$ to nearly $1$, a quadratic improvement over the $O(1/p)$ classical repetitions. Grover's algorithm is the special case $A=H^{\otimes n}$, $R_G=O_{x,\pm}$.
--
--   **Formalization Note** $A^{-1}$ is the conjugate transpose $A^*$ (as $A$ is unitary). $R_G$ is constrained only on $\psi_1$ and $\psi_0$, as in the source. The hypotheses require $m\ge1$, since two orthonormal vectors need dimension at least 2.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, PDF p. 69, §7.3. https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_Defs_Search
set_option autoImplicit false

namespace QAlgorithms.DeWolf

open QAlgorithms


/-- de Wolf §7.3, PDF pp.68–69 (unnumbered): amplitude amplification.

Let `A` be a unitary on `m` qubits with `A|0^m⟩ = √p |ψ₁⟩ + √(1−p) |ψ₀⟩`, where `ψ₁, ψ₀` are
orthogonal unit vectors and `0 < p ≤ 1`, and let `R_G` be a unitary with `R_G ψ₁ = −ψ₁`,
`R_G ψ₀ = ψ₀`. Put `θ = arcsin √p` and `Q = A R_0 A^{-1} R_G` (`A^{-1} = A^*`).
1. For every `k`, `Q^k A|0^m⟩ = sin((2k+1)θ) ψ₁ + cos((2k+1)θ) ψ₀`.
2. If `k` is an integer closest to `π/(4θ) − 1/2`, then `k ≤ π/(4θ) ≤ π/(4√p)` and the
   probability `|⟨ψ₁|Q^k A|0^m⟩|²` of the good state is at least `1 − p`. -/
theorem amplitudeAmplification (m : ℕ) (A RG : Matrix (Qubits m) (Qubits m) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Qubits m) ℂ) (hRG : RG ∈ Matrix.unitaryGroup (Qubits m) ℂ)
    (ψ1 ψ0 : EuclideanSpace ℂ (Qubits m)) (hψ1 : IsState ψ1) (hψ0 : IsState ψ0)
    (horth : inner ℂ ψ1 ψ0 = 0) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hAψ : act A (zeroKet m) =
      (Real.sqrt p : ℂ) • ψ1 + (Real.sqrt (1 - p) : ℂ) • ψ0)
    (hRG1 : act RG ψ1 = -ψ1) (hRG0 : act RG ψ0 = ψ0) :
    (∀ k : ℕ, act (ampAmpIterate A RG (0 : Qubits m) ^ k) (act A (zeroKet m)) =
        (Real.sin ((2 * k + 1) * Real.arcsin (Real.sqrt p)) : ℂ) • ψ1 +
          (Real.cos ((2 * k + 1) * Real.arcsin (Real.sqrt p)) : ℂ) • ψ0) ∧
    ∀ k : ℕ, |(k : ℝ) - (Real.pi / (4 * Real.arcsin (Real.sqrt p)) - 1 / 2)| ≤ 1 / 2 →
      (k : ℝ) ≤ Real.pi / (4 * Real.arcsin (Real.sqrt p)) ∧
      Real.pi / (4 * Real.arcsin (Real.sqrt p)) ≤ Real.pi / (4 * Real.sqrt p) ∧
      1 - p ≤ ‖inner ℂ ψ1 (act (ampAmpIterate A RG (0 : Qubits m) ^ k) (act A (zeroKet m)))‖ ^ 2 := by
  sorry

end QAlgorithms.DeWolf
