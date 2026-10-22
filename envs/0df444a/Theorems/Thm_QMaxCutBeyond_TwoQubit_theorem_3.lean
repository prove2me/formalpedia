-- Prove2me | Theorems.Thm_QMaxCutBeyond_TwoQubit_theorem_3
-- name    : QMaxCutBeyond.TwoQubit.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:14.275154+00:00
-- url     : https://prove2.me/theorems/f9b00fbe-a991-4d10-8159-e40d3509bf0d
-- title:
--   Theorem 3 — on every weighted graph a tensor product of 1- and 2-qubit states reaches 0.55 · OPT(G)
-- statement:
--   Let $G=(V,E,w)$ be a graph with nonnegative edge weights and $H_G=\sum_{\{i,j\}\in E}w_{ij}\frac12(I-X_iX_j-Y_iY_j-Z_iZ_j)$ the quantum Max Cut Hamiltonian, with $\mathrm{OPT}(G)=\|H_G\|$. Then there is a tensor product $\varphi=\varphi_1\otimes\varphi_2\otimes\cdots\otimes\varphi_L$ of 1- and 2-qubit states $\{\varphi_j\}$ such that
--   $$\frac{\langle\varphi|H_G|\varphi\rangle}{\mathrm{OPT}(G)}\;\ge\;0.55 .$$
--
--   Product states cannot beat ratio $1/2$ in general (a single edge), so allowing two-qubit blocks strictly improves the guarantee on every weighted graph.
--
--   **Formalization Note** Stated without division: there is $\varphi$ in the 1-/2-qubit class such that $0.55\,\langle\psi|H_G|\psi\rangle\le\langle\varphi|H_G|\varphi\rangle$ for every unit state $\psi$, with $0.55$ written as the real number $11/20$; this is equivalent to the ratio form when $\mathrm{OPT}(G)>0$, and when all weights vanish both sides are $0$. The state $\varphi$ is chosen before $\psi$. The second sentence of Theorem 3 (an efficient randomized algorithm with ratio $\ge0.53$) is not formalized.
-- source:
--   Anshu, Gosset & Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394v1, p. 5, Theorem 3 (first sentence); proof pp. 9–11

import Mathlib
import Definitions.Def_QMaxCutBeyond_TwoQubit_Setting

namespace QMaxCutBeyond.TwoQubit

/-- Theorem 3 (first sentence), p. 5: for every graph with nonnegative edge weights there is a
tensor product `φ = φ₁ ⊗ ⋯ ⊗ φ_L` of 1- and 2-qubit states with `⟨φ|H_G|φ⟩ / OPT(G) ≥ 0.55`,
stated without division: `0.55 ⟨ψ|H_G|ψ⟩ ≤ ⟨φ|H_G|φ⟩` for every unit state `ψ`. -/
theorem theorem_3 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : ∀ e, 0 ≤ w e) :
    ∃ φ : Config n → ℂ, IsOneTwoProduct φ ∧ ∀ ψ : Config n → ℂ, IsUnitState ψ →
      (11 / 20 : ℝ) * energy (hamiltonian G w) ψ ≤ energy (hamiltonian G w) φ := by sorry

end QMaxCutBeyond.TwoQubit
