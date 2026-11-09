-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_cyclic_constraint
-- name    : QMAPerfectCompleteness.Main.cyclic_constraint
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:59:00.207106+00:00
-- url     : https://prove2.me/theorems/c979843b-ffb4-4aca-b566-92a53f538dcb
-- title:
--   Lemma 3.4 — the cyclic history kernel and its soundness
-- statement:
--   Let $C_{z,\Gamma}$ and $|\Omega_z\rangle$ be the operator and vector of Eq. (3).
--
--   1. On a YES instance, if $\Gamma_z>2$ and $\Gamma=\Gamma_z$, then $|\Omega_z\rangle\ne0$ and
--   $$(I-C_{z,\Gamma})|\Omega_z\rangle=0.$$
--   2. On a NO instance, that is, if every proof is accepted with probability at most $1/3$,
--   $$\|(I-C_{z,\Gamma})|\Psi\rangle\|\ge\tfrac13\||\Psi\rangle\|$$
--   for all $z$, all real $\Gamma\ge2$, and all complex vectors $|\Psi\rangle$, normalized or not, with the Euclidean norm.
--
--   Clause 2 does not assume $\Gamma=\Gamma_z$: it holds for every claimed value. Together the clauses reduce the distinction between YES and NO instances to an exact kernel condition.
--
--   Differences from the source:
--   - generalization: the fixed verifier $V$ of Lemma 3.1 on one input → any verifier $V$ over $\mathcal G_2$, with YES and NO instances being the conditions at $2/3$ and $1/3$ on that verifier, and without the source's $g\ge1$; reason: the statement specializes to the source's verifier on any input in the promise; no property of $g$ is used
--   - encoding: the number $\Gamma_z$ → the real part of the matrix entry $\langle z|A^\ell|z\rangle$; histories are complex functions on the clock/proof basis, with euclidNorm defined as the square root of the sum of squared absolute values; reason: $A^\ell$ is Hermitian, so the entry is real, and this is exactly the finite-dimensional Euclidean norm
-- source:
--   Sabee Grewal, Dorian Rudolph, QMA has perfect completeness, STOC 2027 submission #490 (October 2026), p. 8, Lemma 3.4, Eq. (3)

import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic

open Matrix

namespace QMAPerfectCompleteness.Main

/-- Lemma 3.4 (p. 8). (i) On a YES instance, if `Γ_z > 2` and `Γ = Γ_z`, then `|Ω_z⟩ ≠ 0` satisfies
`(I - C_{z,Γ})|Ω_z⟩ = 0`. (ii) On a NO instance (`E ⪯ I/3`),
`‖(I - C_{z,Γ})|Ψ⟩‖ ≥ (1/3)‖|Ψ⟩‖` for all `z`, all `Γ ≥ 2` and all `|Ψ⟩`. -/
theorem cyclic_constraint (V : Verifier gatesG2) :
    (V.AcceptsSomeProof (2 / 3) → ∀ (z : V.Proof) (Γ : ℝ), 2 < V.gamma z → Γ = V.gamma z →
      V.historyVector z ≠ 0 ∧ (1 - V.cyclicOp z Γ) *ᵥ V.historyVector z = 0) ∧
    (V.AcceptsAllProofsAtMost (1 / 3) → ∀ (z : V.Proof) (Γ : ℝ), 2 ≤ Γ → ∀ Ψ : History V → ℂ,
      (1 / 3) * euclidNorm Ψ ≤ euclidNorm ((1 - V.cyclicOp z Γ) *ᵥ Ψ)) := by sorry

end QMAPerfectCompleteness.Main
