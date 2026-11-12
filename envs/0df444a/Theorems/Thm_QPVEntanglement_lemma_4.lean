-- Prove2me | Theorems.Thm_QPVEntanglement_lemma_4
-- name    : QPVEntanglement.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:36:01.826342+00:00
-- url     : https://prove2.me/theorems/b92d0a75-9e2d-4491-afc5-9d267109f94a
-- title:
--   Lemma 4 — BB84 success implies Bell fidelity
-- statement:
--   This mission states the paper's results in the **operator-requested pinned-down model** of its §4 adversary model; this item is a pure quantum-information statement and does not depend on that model.
--
--   Let $\{q_x,\rho^{(x)}_{AB}\}$ be a finite ensemble of two-qubit states and let $p_x$ be the probability that $\rho^{(x)}$ passes the random two-qubit BB84 test (basis $ZZ$ or $XX$ with probability $\tfrac12$ each, pass iff the outcomes agree), $p=\sum_xq_xp_x$. Then
--
--   $$F_{avg}:=\sum_xq_x\langle\Phi^+|\rho^{(x)}_{AB}|\Phi^+\rangle\ge 2p-1.$$
--
--   It converts the verifiers' test statistics into the Bell fidelities used by Theorem 6.
--
--   Differences from the source:
--   - encoding: random two-qubit BB84 verification test (measuring both qubits in a randomly chosen XX or ZZ basis) → p_x = ½ tr(Π_Z ρ) + ½ tr(Π_X ρ), Π_Z = |00⟩⟨00|+|11⟩⟨11|, Π_X = (H⊗H)Π_Z(H⊗H); reason: the proof's eq. (59), p.64, fixes the test this way; Π_X = Φ⁺ + Ψ⁺ as on p.64
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Lemma 4, eq. (5), pp.32–33; proof p.64

import Mathlib
import Definitions.Def_QPVEntanglement_flaggedState
import Definitions.Def_QPVEntanglement_bb84TestProb

set_option autoImplicit false

open scoped Matrix ComplexOrder

namespace QPVEntanglement

/-- **Lemma 4 (BB84 Success Implies Bell Fidelity)**, pp.32–33 (proof p.64). Behera–Goyal,
arXiv:2609.39234 (sha256 bdf2928d…), Lemma 4, eq. (5), p.33.

For a probabilistic ensemble `{q_x, ρ^{(x)}_{AB}}` of two-qubit states whose average success
probability in the random two-qubit BB84 test is `p = Σ_x q_x p_x`,
`F_avg = Σ_x q_x ⟨Φ⁺|ρ^{(x)}_{AB}|Φ⁺⟩ ≥ 2p − 1`.

**Formalization Note.** `p_x = bb84TestProb ρ^{(x)} = ½ tr(Π_Z ρ) + ½ tr(Π_X ρ)` (eq. (59),
p.64); the ensemble index set is finite. -/
theorem lemma_4 {X : Type*} [Fintype X] (q : X → ℝ)
    (ρ : X → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hq : IsProbVec q)
    (hρ : ∀ x, IsDensity (ρ x)) :
    2 * (∑ x, q x * bb84TestProb (ρ x)) - 1 ≤ ∑ x, q x * bellOverlap (ρ x) := by sorry

end QPVEntanglement
