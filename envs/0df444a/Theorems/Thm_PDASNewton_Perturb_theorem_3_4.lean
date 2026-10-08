-- Prove2me | Theorems.Thm_PDASNewton_Perturb_theorem_3_4
-- name    : PDASNewton.Perturb.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:11:42.684317+00:00
-- url     : https://prove2.me/theorems/0dbfc1a1-bad5-4310-970b-076a0d407b04
-- title:
--   Theorem 3.4, p. 9 — for A = M + K, M an M-matrix and ‖K‖₁ small: unique solution, well-defined algorithm, xᵏ → x*
-- statement:
--   Let $M \in \mathbb{R}^{n\times n}$ be an M-matrix (nonsingular, $m_{ij}\le 0$ for $i\ne j$, $M^{-1}\ge 0$), and write $\|K\|_1 = \max_j \sum_i |k_{ij}|$ for the matrix norm subordinate to the one-norm. Consider, for $f,\psi\in\mathbb{R}^n$ and $c>0$, the complementarity problem (3.1)
--   $$Ay + \lambda = f, \qquad \lambda - \max(0, \lambda + c(y-\psi)) = 0$$
--   with $A = M + K$, and the primal-dual active set algorithm: from $(y^k,\lambda^k)$ set $\mathcal{A}_k = \{i : \lambda^k_i + c(y^k-\psi)_i > 0\}$, $\mathcal{I}_k$ its complement, and solve $Ay^{k+1} + \lambda^{k+1} = f$, $y^{k+1} = \psi$ on $\mathcal{A}_k$, $\lambda^{k+1} = 0$ on $\mathcal{I}_k$. (Calligraphic $\mathcal{A}$ is an index set, distinct from the matrix $A$.)
--
--   **Theorem 3.4.** There is $\varepsilon > 0$ such that for every $K$ with $\|K\|_1 < \varepsilon$, every $f,\psi\in\mathbb{R}^n$ and every $c>0$:
--   1. (3.1) admits a unique solution $x^* = (y^*,\lambda^*)$;
--   2. the algorithm is well-defined: from any $(y^k,\lambda^k)$ the step has exactly one solution $(y^{k+1},\lambda^{k+1})$;
--   3. for arbitrary initial data $(y^0,\lambda^0)$ the iterates converge, $$\lim_{k\to\infty} x^k = x^* .$$
--
--   The M-matrix property is not stable under small perturbations, since off-diagonal entries may become positive; the theorem shows that global convergence of the algorithm, known for M-matrices (Theorem 3.2), survives them. Its conclusion also implies that $M+K$ is a P-matrix.
--
--   **Formalization Note** "If $\|K\|_1$ is sufficiently small" is read as a single $\varepsilon>0$ depending only on $M$ (and $n$), quantified before $f$, $\psi$, $c$ and the initial data; the proof's smallness conditions involve only $M$ and $K$, and the paper itself deduces from the theorem solvability of (3.1) for arbitrary $f$. The matrix $M+K$ is not assumed to be a P-matrix, and no invertibility of its principal blocks is assumed: both are consequences. Convergence is in the product topology of $\mathbb{R}^n\times\mathbb{R}^n$ and is stated for every solution, which by conclusion 1 is the solution. A run is an infinite sequence of steps (the "Stop" option is not modelled).
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 9, Theorem 3.4

import Mathlib
import Definitions.Def_PDASNewton_Perturb_Setting

open Filter Topology Matrix

namespace PDASNewton.Perturb

theorem theorem_3_4 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsMMatrix M) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ K : Matrix (Fin n) (Fin n) ℝ, oneNorm K < ε →
      ∀ (f ψ : Fin n → ℝ) (c : ℝ), 0 < c →
        (∃! p : (Fin n → ℝ) × (Fin n → ℝ), PDASNewton.Local.IsSolution (M + K) f ψ c p.1 p.2) ∧
        (∀ y lam : Fin n → ℝ,
          ∃! q : (Fin n → ℝ) × (Fin n → ℝ), PDASNewton.Local.IsStep (M + K) f ψ c y lam q.1 q.2) ∧
        (∀ ystar lamstar : Fin n → ℝ, PDASNewton.Local.IsSolution (M + K) f ψ c ystar lamstar →
          ∀ y lam : ℕ → Fin n → ℝ, PDASNewton.Local.IsRun (M + K) f ψ c y lam →
            Tendsto (fun k => (y k, lam k)) atTop (𝓝 (ystar, lamstar))) := by sorry

end PDASNewton.Perturb
