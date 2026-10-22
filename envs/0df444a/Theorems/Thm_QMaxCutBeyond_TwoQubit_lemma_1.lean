-- Prove2me | Theorems.Thm_QMaxCutBeyond_TwoQubit_lemma_1
-- name    : QMaxCutBeyond.TwoQubit.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:04.598639+00:00
-- url     : https://prove2.me/theorems/cdaaf7f2-7506-43c8-9cf5-e8b2e5b04db9
-- title:
--   Lemma 1 — on a star with nonnegative weights, every unit state has energy at most max_e w_e + Σ_e w_e
-- statement:
--   Let $G=(V,E,w)$ be a star graph with nonnegative weights and $H_G$ the quantum Max Cut Hamiltonian. Then
--   $$\|H_G\|\;\le\;\max_{e\in E}w_e+\sum_{e\in E}w_e .$$
--
--   The trivial bound is $2\sum_e w_e$; the lemma says the centre qubit cannot be maximally entangled with all leaves at once (monogamy of entanglement). Applied to the star of each vertex it gives the upper bound on $\mathrm{OPT}(G)$ used in Theorems 3 and 5.
--
--   **Formalization Note** Stated as: every unit state $\psi$ has $\langle\psi|H_G|\psi\rangle\le\max_e w_e+\sum_e w_e$. Since $H_G\succeq0$, this is equivalent to the norm bound. A star is a graph all of whose edges contain a centre $c$; other vertices may be isolated (their qubits are idle), which is the situation in which the lemma is applied.
-- source:
--   Anshu, Gosset & Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394v1, p. 6, Lemma 1, eq. (9)

import Mathlib
import Definitions.Def_QMaxCutBeyond_TwoQubit_Setting

namespace QMaxCutBeyond.TwoQubit

/-- Lemma 1, p. 6: for a star graph with nonnegative weights, `‖H_G‖ ≤ max_{e∈E} w_e +
Σ_{e∈E} w_e`, stated as: every unit state has energy at most that bound. -/
theorem lemma_1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : ∀ e, 0 ≤ w e) (c : Fin n) (hstar : IsStar G c)
    (ψ : Config n → ℂ) (hψ : IsUnitState ψ) :
    energy (hamiltonian G w) ψ ≤ maxEdgeWeight G w + totalWeight G w := by sorry

end QMaxCutBeyond.TwoQubit
