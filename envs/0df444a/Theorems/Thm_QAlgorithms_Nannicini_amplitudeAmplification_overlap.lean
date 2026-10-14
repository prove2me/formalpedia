-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_amplitudeAmplification_overlap
-- name    : QAlgorithms.Nannicini.amplitudeAmplification_overlap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:45:51.568682+00:00
-- url     : https://prove2.me/theorems/58b459f9-8ba1-4348-a498-294b653cac62
-- title:
--   Amplitude amplification: overlap 2/3 with the good state using O(1/√p) applications of S and R
-- statement:
--   Let $S$ be a unitary on $n$ qubits and write $S|\vec 0\rangle=\sum_{j\in\{0,1\}^n}\alpha_j|j\rangle$. Fix a set $M\subseteq\{0,1\}^n$ of good basis states, let $p=\sum_{j\in M}|\alpha_j|^2$ and assume $0<p<1$ (equivalently, $S|\vec 0\rangle=\sin\theta\,|\psi_G\rangle+\cos\theta\,|\psi_B\rangle$ with $\theta\in(0,\pi/2)$), where
--
--   $$|\psi_G\rangle=\frac{1}{\sqrt p}\sum_{j\in M}\alpha_j|j\rangle,\qquad |\psi_B\rangle=\frac{1}{\sqrt{1-p}}\sum_{j\notin M}\alpha_j|j\rangle.$$
--
--   Let $R$ be an $n$-qubit unitary with $R|\psi_G\rangle=-|\psi_G\rangle$ and $R|\psi_B\rangle=|\psi_B\rangle$. Let $F=2|\vec 0\rangle\langle\vec 0|-I$ and let $G=SFS^\dagger R$ be the Grover iteration. Then there is an absolute constant $C>0$ (independent of $n$, $S$, $M$, $R$ and $p$) such that for every such data some number of iterations $k\in\mathbb N$ satisfies
--
--   $$2k+1\le\frac{C}{\sqrt p}\qquad\text{and}\qquad\bigl|\langle\psi_G|\,G^k S|\vec 0\rangle\bigr|\ge\frac23.$$
--
--   The algorithm uses $2k+1$ applications of $S$ or $S^\dagger$ and $k$ applications of $R$, so the total is $O(1/\sqrt p)$. This is the basic quadratic speedup of amplitude amplification over classical repetition, which needs $O(1/p)$ runs.
--
--   **Formalization Note** The overlap is the modulus of the inner product, not its square: the squared reading is false at $p=1/2$, where $|\sin((2k+1)\pi/4)|^2=1/2$ for every $k$. The additional gates (the reflection $F$) carry no bound in the source and are not counted. The constant is quantified before all data, and no threshold on $p$ is needed since $1/\sqrt p>1$.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 78, Theorem 4.6. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
set_option autoImplicit false

namespace QAlgorithms.Nannicini

/-- Nannicini p.78–79, Theorem 4.6 (Amplitude amplification; Brassard et al. 2002). Let `S` be an
`n`-qubit unitary with `S|0⟩ = √p |ψ_G⟩ + √(1 − p) |ψ_B⟩`, where for a set `M ⊆ {0,1}^n`,
`|ψ_G⟩ = (1/√p) ∑_{j ∈ M} α_j |j⟩`, `|ψ_B⟩ = (1/√(1−p)) ∑_{j ∉ M} α_j |j⟩` and
`p = ∑_{j ∈ M} |α_j|²` (here `α = S|0⟩`), with `0 < p < 1` (§4.1.4, p.77: `θ ∈ (0, π/2)`). Let `R`
be a unitary with `R|ψ_G⟩ = −|ψ_G⟩` and `R|ψ_B⟩ = |ψ_B⟩`. Then the amplitude amplification
algorithm, i.e. `k` Grover iterations `G = S F S† R` applied to `S|0⟩` (p.77), produces a state
whose overlap `|⟨ψ_G|G^k S|0⟩|` with `|ψ_G⟩` is at least `2/3`, using `O(1/√p)` applications of
`S` and `R`: the `2k + 1` applications of `S` or `S†` are at most `C/√p` for a constant `C`
chosen before `n, S, M, R, p`. -/
theorem amplitudeAmplification_overlap :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (S R : Matrix (Qubits n) (Qubits n) ℂ) (M : Finset (Qubits n)),
      S ∈ Matrix.unitaryGroup (Qubits n) ℂ → R ∈ Matrix.unitaryGroup (Qubits n) ℂ →
      0 < probEvent (act S (zeroKet n)) (fun j => j ∈ M) →
      probEvent (act S (zeroKet n)) (fun j => j ∈ M) < 1 →
      act R (ampGoodState (act S (zeroKet n)) M) = -ampGoodState (act S (zeroKet n)) M →
      act R (ampBadState (act S (zeroKet n)) M) = ampBadState (act S (zeroKet n)) M →
      ∃ k : ℕ,
        (2 * (k : ℝ) + 1) ≤ C / Real.sqrt (probEvent (act S (zeroKet n)) (fun j => j ∈ M)) ∧
        2 / 3 ≤ ‖inner ℂ (ampGoodState (act S (zeroKet n)) M)
          (act (ampAmpIterate S R 0 ^ k) (act S (zeroKet n)))‖ := by
  sorry





end QAlgorithms.Nannicini
