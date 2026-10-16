-- Prove2me | Theorems.Thm_QSPHamSim_Main_achievable_AC
-- name    : QSPHamSim.Main.achievable_AC
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:08.937727+00:00
-- url     : https://prove2.me/theorems/d4f5e1d0-93ea-4412-9f07-950874ebe5d9
-- title:
--   Theorem 1 — characterization of achievable A and C
-- statement:
--   Let $N>0$ be even and let $A,C:\mathbb R\to\mathbb R$. There are $N$ real phases whose qubit rotation sequence has Pauli components $A$ and $C$ at every angle if and only if
--   $$
--   A(0)=1,\qquad A(\theta)^2+C(\theta)^2\le1\quad(\theta\in\mathbb R),
--   $$
--   and $A$ is a cosine series with frequencies $0,\ldots,N/2$ while $C$ is a sine series with frequencies $1,\ldots,N/2$.
--
--   This is the exact realizability criterion used to turn approximating functions into a signal-processing circuit. The paper quotes it from earlier work.
--
--   **Formalization Note** The theorem states existence and both directions of the criterion. The paper's further claim that phases can be efficiently computed is not part of this statement.
-- source:
--   Low, Chuang, Optimal Hamiltonian Simulation by Quantum Signal Processing, arXiv:1606.02685v2, p. 3, Theorem 1

import Mathlib
import Definitions.Def_QSPHamSim_Main_Setting

set_option autoImplicit false

namespace QSPHamSim.Main

theorem achievable_AC (N : ℕ) (hN : 0 < N) (hNeven : Even N)
    (A C : ℝ → ℝ) :
    (∃ φ : Fin N → ℝ, ∀ θ : ℝ,
      compA (qspSeq N φ θ) = A θ ∧ compC (qspSeq N φ θ) = C θ) ↔
    (∀ θ : ℝ, A θ ^ 2 + C θ ^ 2 ≤ 1) ∧
      A 0 = 1 ∧ IsCosSeries (N / 2) A ∧ IsSinSeries (N / 2) C := by sorry

end QSPHamSim.Main
