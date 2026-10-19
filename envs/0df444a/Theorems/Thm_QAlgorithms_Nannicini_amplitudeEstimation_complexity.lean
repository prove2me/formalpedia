-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_amplitudeEstimation_complexity
-- name    : QAlgorithms.Nannicini.amplitudeEstimation_complexity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:46:21.033832+00:00
-- url     : https://prove2.me/theorems/2b59680e-1f43-4f6f-91dd-61381cdce892
-- title:
--   Amplitude estimation to additive error ε with O(log 1/ε) qubits and O(1/ε) queries
-- statement:
--   This is the complexity statement of amplitude estimation.
--
--   There is a constant $C > 0$ such that for every $\epsilon \in (0,1)$ there is a number $m$ of phase-estimation qubits with
--   $$m \le C\left(\log_2 \frac{1}{\epsilon} + 1\right), \qquad 3(2^m - 1) + 1 \le \frac{C}{\epsilon},$$
--   such that for every input of amplitude estimation (an $n$-qubit unitary $S$ with $S|\vec 0\rangle = \sin\theta|\psi_G\rangle + \cos\theta|\psi_B\rangle$, orthogonal states $|\psi_G\rangle, |\psi_B\rangle$, $\theta \in [0, \tfrac{\pi}{2}]$, and a unitary $R$ with $R|\psi_G\rangle = -|\psi_G\rangle$, $R|\psi_B\rangle = |\psi_B\rangle$) the estimate $\tilde a = \sin^2\tilde\theta$ returned by the $m$-qubit algorithm satisfies
--   $$\Pr\left[\,|\sin^2\theta - \tilde a| \le \epsilon\,\right] \ge \frac{8}{\pi^2}.$$
--   Here $3(2^m-1)+1$ is the number of calls to $S$, $S^\dagger$ and $CR$ made by the $m$-qubit circuit: $2^m - 1$ controlled Grover operators, each using $S$, $S^\dagger$ and $CR$ once, plus the initial $S$.
--
--   Compared with the $O(1/\epsilon^2)$ samples of classical Monte Carlo estimation, this is a quadratic speedup.
--
--   **Formalization Note** The choice of $m$ depends only on $\epsilon$ and precedes the input. The success probability $8/\pi^2$ is not printed in the corollary; it is the probability of Proposition 4.21, from which the corollary is said to follow. The query count is the explicit count of the circuit of Fig. 4.9 (p.86).
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 88, Corollary 4.22. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
set_option autoImplicit false

namespace QAlgorithms.Nannicini




/-- Nannicini p.88, Corollary 4.22: to estimate the probability `sin²θ` of obtaining `|ψ_G⟩` from a
measurement of `S|0⟩` with absolute error at most `ϵ` by amplitude estimation, it suffices to use
`m = O(log 1/ϵ)` qubits for phase estimation, leading to `O(1/ϵ)` queries to the input unitaries
`S` and `CR`. Formally: there is a constant `C > 0` such that for every `ϵ ∈ (0, 1)` there is an
`m` (chosen before the input `n, S, R, θ, ψ_G, ψ_B`) with `m ≤ C (log₂(1/ϵ) + 1)` and with the
number `3(2^m − 1) + 1` of calls to `S`, `S†` and `CR` made by the `m`-qubit circuit (p.86: `2^m − 1`
controlled Grover operators, each with one `S`, one `S†` and one `CR`, plus the initial `S`) at
most `C/ϵ`, such that for every input of §4.3 the estimate `ã = sin²θ̃` of Prop. 4.21's algorithm
satisfies `|sin²θ − ã| ≤ ϵ` with probability at least `8/π²` (the success probability of
Prop. 4.21, from which the corollary follows). -/
theorem amplitudeEstimation_complexity :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ m : ℕ, (m : ℝ) ≤ C * (Real.logb 2 (1 / ε) + 1) ∧
        ((3 * (2 ^ m - 1) + 1 : ℕ) : ℝ) ≤ C / ε ∧
        ∀ (n : ℕ) (S R : Matrix (Qubits n) (Qubits n) ℂ)
          (psiG psiB : EuclideanSpace ℂ (Qubits n)) (θ : ℝ),
          S ∈ Matrix.unitaryGroup (Qubits n) ℂ → R ∈ Matrix.unitaryGroup (Qubits n) ℂ →
          IsState psiG → IsState psiB → inner ℂ psiG psiB = 0 →
          0 ≤ θ → θ ≤ Real.pi / 2 →
          act S (zeroKet n) = (Real.sin θ : ℂ) • psiG + (Real.cos θ : ℂ) • psiB →
          act R psiG = -psiG → act R psiB = psiB →
          8 / Real.pi ^ 2 ≤ probEvent (aeState m S R) fun z =>
            |Real.sin θ ^ 2 - Real.sin (aeAngle z.1) ^ 2| ≤ ε := by
  sorry

end QAlgorithms.Nannicini
