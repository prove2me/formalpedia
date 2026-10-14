-- Prove2me | Theorems.Thm_QAlgorithms_Childs_adiabatic_theorem
-- name    : QAlgorithms.Childs.adiabatic_theorem
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:35:23.137372+00:00
-- url     : https://prove2.me/theorems/54b10ad9-502e-44da-9e52-ed605efc634f
-- title:
--   Quantitative adiabatic theorem
-- statement:
--   This is the quantitative quantum adiabatic theorem.
--
--   There are absolute constants $c_1, c_2, c_3 > 0$ (the constants of the first- and second-order perturbation bounds $\|\dot P\| \le c_1 \|\dot H\|/\Delta$ and $\|\ddot P\| \le c_2\|\ddot H\|/\Delta + c_3\|\dot H\|^2/\Delta^2$) with the following property. Let $\mathcal H = \mathbb C^{d}$ be a finite-dimensional Hilbert space with $d \ge 2$, and let $H(s)$, $s \in [0,1]$, be a twice continuously differentiable family of Hermitian operators on $\mathcal H$, with derivatives $\dot H(s)$ and $\ddot H(s)$ (one-sided at the endpoints). Suppose that for every $s \in [0,1]$ the ground state of $H(s)$ is nondegenerate, and let $\Delta(s) > 0$ be the gap between the smallest eigenvalue $E(s)$ of $H(s)$ and the nearest distinct eigenvalue. Norms of operators are spectral norms. Let $\epsilon > 0$ and let the total evolution time $T$ satisfy
--
--   $$
--   T \ge \frac{2}{\epsilon}\left[c_1\frac{\|\dot H(0)\|}{\Delta(0)^2} + c_1\frac{\|\dot H(1)\|}{\Delta(1)^2} + \int_0^1 \left((3c_1^2 + c_1 + c_3)\frac{\|\dot H(s)\|^2}{\Delta(s)^3} + c_2\frac{\|\ddot H(s)\|}{\Delta(s)^2}\right) ds\right].
--   $$
--
--   If $|\psi(s)\rangle$ solves the Schrödinger equation $i\,\frac{d}{ds}|\psi(s)\rangle = T\,H(s)|\psi(s)\rangle$ on $[0,1]$ and $|\psi(0)\rangle$ is a unit ground state of $H(0)$, then there is a unit ground state $|\phi(1)\rangle$ of $H(1)$ with
--
--   $$
--   \big\|\,|\psi(1)\rangle - |\phi(1)\rangle\,\big\| \le \epsilon.
--   $$
--
--   The theorem quantifies how slowly a Hamiltonian must be varied for a system started in its ground state to end close to the final ground state, with the required time governed by the spectral gap; it underlies adiabatic optimization and adiabatic quantum computation.
--
--   **Formalization Note** The instantaneous ground state $|\phi(1)\rangle$ is fixed only up to a global phase, so the conclusion asserts the existence of some unit ground state of $H(1)$ within $\epsilon$. The constants are quantified before the dimension and the Hamiltonian. The derivatives $\dot H, \ddot H$ are given as functions with derivative-within-$[0,1]$ hypotheses and $\ddot H$ continuous; the gap is the difference of the two smallest eigenvalues counted with multiplicity, which equals the source's $\Delta$ when the ground state is nondegenerate.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF p. 163, Theorem 30.1. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Hamiltonian
set_option autoImplicit false

namespace QAlgorithms.Childs

/-- Childs, Theorem 30.1 (PDF p.163, eq. (30.49)–(30.50)): the quantitative adiabatic theorem.
There are constants `c₁, c₂, c₃` (those of the perturbation bounds (30.46)–(30.47), PDF p.162;
absolute, so quantified before the dimension and the Hamiltonian) such that the following holds.
Let `H(s)`, `s ∈ [0, 1]`, be a twice continuously differentiable family of Hermitian operators
with a nondegenerate ground state for every `s ∈ [0, 1]` (gap `∆(s) > 0`), let `ϵ > 0` and
`T ≥ (2/ϵ)[c₁‖Ḣ(0)‖/∆(0)² + c₁‖Ḣ(1)‖/∆(1)² + ∫₀¹ ((3c₁² + c₁ + c₃)‖Ḣ‖²/∆³ + c₂‖Ḧ‖/∆²) ds]`.
If `ψ` solves `i dψ/ds = T H(s) ψ(s)` on `[0, 1]` with `ψ(0)` a (unit) ground state of `H(0)`,
then `‖ψ(1) − ϕ(1)‖ ≤ ϵ` for a ground state `ϕ(1)` of `H(1)`; the instantaneous ground state is
fixed only up to a phase (PDF p.160), so the conclusion asserts some unit ground state of `H(1)`. -/
theorem adiabatic_theorem :
    ∃ c1 c2 c3 : ℝ, 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H H1 H2 : ℝ → Matrix ι ι ℂ),
        (∀ s ∈ Set.Icc (0 : ℝ) 1, HasSimpleGroundState (H s)) →
        (∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt H (H1 s) (Set.Icc 0 1) s) →
        (∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt H1 (H2 s) (Set.Icc 0 1) s) →
        ContinuousOn H2 (Set.Icc 0 1) →
        ∀ ε : ℝ, 0 < ε →
        ∀ T : ℝ,
          T ≥ 2 / ε * (c1 * specNorm (H1 0) / spectralGap (H 0) ^ 2 +
            c1 * specNorm (H1 1) / spectralGap (H 1) ^ 2 +
            ∫ s in (0 : ℝ)..1,
              ((3 * c1 ^ 2 + c1 + c3) * specNorm (H1 s) ^ 2 / spectralGap (H s) ^ 3 +
                c2 * specNorm (H2 s) / spectralGap (H s) ^ 2)) →
        ∀ ψ : ℝ → EuclideanSpace ℂ ι,
          SolvesScaledSchrodinger H T ψ →
          IsGroundState (H 0) (ψ 0) →
          ∃ φ1 : EuclideanSpace ℂ ι, IsGroundState (H 1) φ1 ∧ ‖ψ 1 - φ1‖ ≤ ε := by
  sorry

end QAlgorithms.Childs
