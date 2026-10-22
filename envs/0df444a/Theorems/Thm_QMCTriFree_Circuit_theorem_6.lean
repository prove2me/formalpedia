-- Prove2me | Theorems.Thm_QMCTriFree_Circuit_theorem_6
-- name    : QMCTriFree.Circuit.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:24.210062+00:00
-- url     : https://prove2.me/theorems/a31875f4-16e0-49c9-b353-2c6348cd5e6a
-- title:
--   Theorem 6 — $\mathrm{Lasserre}_2(H)$ upper bounds QMC: every state gives a feasible $M$ with the same energy, so $\mathrm{Lasserre}_2(H)\ge\|H\|$
-- statement:
--   For every weighted graph:
--   1. every unit vector $\psi$ induces a feasible matrix $M$ of $\mathrm{Lasserre}_2(H)$ whose objective equals $\langle\psi|H|\psi\rangle$;
--   2. consequently every solution $M$ of $\mathrm{Lasserre}_2(H)$ has objective at least $\|H\|$:
--   $$\mathrm{Lasserre}_2(H)\ \ge\ \|H\| .$$
--
--   This is the relaxation property used in the last step of the proof of Theorem 19.
--
--   **Formalization Note** Only the QMC, level-2 case is stated, in the concrete form the paper gives on p. 6 (a density matrix induces a feasible matrix with the same energy). "Efficiently computable" is not formalized. The statement is made for arbitrary real weights, which the argument does not need to restrict.
-- source:
--   King, An Improved Approximation Algorithm for Quantum Max-Cut on Triangle-Free Graphs, arXiv:2209.02589v3, p. 7, Theorem 6 (relaxation argument p. 6)

import Mathlib
import Definitions.Def_QMCTriFree_Circuit_Lasserre

set_option autoImplicit false

open QMCProduct.HalfApprox Matrix MeasureTheory ProbabilityTheory

namespace QMCTriFree.Circuit

/-- King, arXiv:2209.02589v3, p. 7, Theorem 6 (QMC, `d = 2`), in the form of p. 6: every unit
state `ψ` induces a feasible `M` of `Lasserre_2(H)` with objective `⟨ψ|H|ψ⟩`; hence every
optimal `M` has objective at least `‖H‖`. -/
theorem theorem_6 {n : ℕ} (w : Fin n → Fin n → ℝ) :
    (∀ ψ : UnitVec n, ∃ M : Matrix (P2 n) (P2 n) ℝ,
        IsFeasible M ∧ lasserreObj w M = (expect (qmcH w) ψ.1).re) ∧
      ∀ M : Matrix (P2 n) (P2 n) ℝ, IsOptimal w M → qmcValue w ≤ lasserreObj w M := by sorry

end QMCTriFree.Circuit
