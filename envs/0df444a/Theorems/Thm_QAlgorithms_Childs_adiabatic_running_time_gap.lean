-- Prove2me | Theorems.Thm_QAlgorithms_Childs_adiabatic_running_time_gap
-- name    : QAlgorithms.Childs.adiabatic_running_time_gap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:36:14.102983+00:00
-- url     : https://prove2.me/theorems/975e3c73-6261-4250-a167-f38e520200d2
-- title:
--   Adiabatic optimization: running time in terms of the minimum gap (linear interpolation)
-- statement:
--   This is the running-time bound for adiabatic optimization with a linear interpolation schedule.
--
--   Let $h:\{0,1\}^n\to\mathbb R$ be a cost function on $n$-bit strings and let
--   $$H_P=\sum_{z\in\{0,1\}^n} h(z)\,|z\rangle\langle z|$$
--   be the problem Hamiltonian. Let $H_B$ be a beginning Hamiltonian on $n$ qubits and let $H(s)=(1-s)H_B+sH_P$ for $s\in[0,1]$. Assume that $H(s)$ is Hermitian and has a nondegenerate ground state for every $s\in[0,1]$. Write $\Delta(s)$ for the gap between the ground and first excited energies of $H(s)$, and $\Delta_{\min}=\min_{s\in[0,1]}\Delta(s)$. Norms of operators are operator norms.
--
--   There are absolute constants $c_1,c_3>0$ (the constants of the first- and second-order perturbation bounds used in the adiabatic theorem, Theorem 30.1) such that the following holds for every such $n$, $h$, $H_B$. Let $\epsilon>0$ and suppose
--   $$T\ \ge\ \frac{2}{\epsilon}\left(2c_1\frac{\|H_P-H_B\|}{\Delta_{\min}^2}+(3c_1^2+c_1+c_3)\frac{\|H_P-H_B\|^2}{\Delta_{\min}^3}\right).$$
--   If $|\psi(s)\rangle$ solves the Schrödinger equation $i\,\frac{d}{ds}|\psi(s)\rangle=T\,H(s)|\psi(s)\rangle$ on $[0,1]$ and $|\psi(0)\rangle$ is a unit-norm ground state of $H_B$, then there is a unit-norm ground state $|\phi(1)\rangle$ of $H_P$ with
--   $$\big\||\psi(1)\rangle-|\phi(1)\rangle\big\|\le\epsilon.$$
--
--   The bound reduces the question of how long the adiabatic algorithm must run to a spectral question: if $\|H_P-H_B\|$ is polynomially bounded and $1/\Delta_{\min}$ is polynomially bounded in $n$, the running time is polynomial.
--
--   **Formalization Note** The ground state of $H_P$ is determined only up to a global phase, so the conclusion asserts the existence of some unit ground state of $H_P$ within distance $\epsilon$. The constants $c_1,c_3$ are quantified existentially before all other data, as in the source, where they are introduced as "some constants". The minimum gap is the infimum of the gap over $[0,1]$.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF p. 166, Theorem 31.1. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Hamiltonian
set_option autoImplicit false

namespace QAlgorithms.Childs

/-- Childs, Theorem 31.1 (PDF p.166, eq. (31.9)): the running time of adiabatic optimization with
linear interpolation, in terms of the minimum gap. There are constants `c₁, c₃ > 0` (those of the
perturbation bounds (30.46)–(30.47), PDF p.162, introduced there as "some constants"; absolute,
so quantified before `n`, `h` and `H_B`) such that the following holds. Let `h : {0,1}ⁿ → ℝ`,
`H_P = Σ_z h(z)|z⟩⟨z|`, and let `H_B` be a beginning Hamiltonian on `n` qubits such that
`H(s) = (1 − s) H_B + s H_P` has a nondegenerate ground state for every `s ∈ [0, 1]` (the standing
assumption of §31.1, PDF p.166; it makes every `H(s)`, in particular `H_B = H(0)`, Hermitian).
Let `ϵ > 0` and
`T ≥ (2/ϵ)(2c₁‖H_P − H_B‖/∆min² + (3c₁² + c₁ + c₃)‖H_P − H_B‖²/∆min³)`. If `ψ` solves
`i dψ/ds = T H(s) ψ(s)` on `[0, 1]` with `ψ(0)` a unit ground state of `H_B`, then
`‖ψ(1) − ϕ(1)‖ ≤ ϵ` for a unit ground state `ϕ(1)` of `H_P` (the ground state is fixed only up to a
phase, PDF p.160, so the conclusion asserts some unit ground state). -/
theorem adiabatic_running_time_gap :
    ∃ c1 c3 : ℝ, 0 < c1 ∧ 0 < c3 ∧
      ∀ (n : ℕ) (h : Qubits n → ℝ) (HB : Matrix (Qubits n) (Qubits n) ℂ),
        (∀ s ∈ Set.Icc (0 : ℝ) 1, HasSimpleGroundState (linInterp HB (problemHamiltonian h) s)) →
        ∀ ε : ℝ, 0 < ε →
        ∀ T : ℝ,
          T ≥ 2 / ε * (2 * c1 * specNorm (problemHamiltonian h - HB) /
              minGap (linInterp HB (problemHamiltonian h)) ^ 2 +
            (3 * c1 ^ 2 + c1 + c3) * specNorm (problemHamiltonian h - HB) ^ 2 /
              minGap (linInterp HB (problemHamiltonian h)) ^ 3) →
        ∀ ψ : ℝ → EuclideanSpace ℂ (Qubits n),
          SolvesScaledSchrodinger (linInterp HB (problemHamiltonian h)) T ψ →
          IsGroundState HB (ψ 0) →
          ∃ φ1 : EuclideanSpace ℂ (Qubits n),
            IsGroundState (problemHamiltonian h) φ1 ∧ ‖ψ 1 - φ1‖ ≤ ε := by
  sorry

end QAlgorithms.Childs
