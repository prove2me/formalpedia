-- Prove2me | Theorems.Thm_SingleInteraction_Supplement_theorem_80
-- name    : SingleInteraction.Supplement.theorem_80
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:15:59.075033+00:00
-- url     : https://prove2.me/theorems/45f92115-6d77-43c0-8a93-de92b08f4bc5
-- title:
--   Theorem 80 — a fixed 9-local positive-semidefinite interaction for which FF-SIH$_9$ is QMA-complete
-- statement:
--   There is a fixed positive-semidefinite 9-qubit interaction $h^{(9)}_{\mathrm{ff}}$ with polynomial-time computable entries such that FF-SIH$_9$ with this interaction is QMA-complete: deciding whether $\lambda_{\min}(H)=0$ (a frustration-free instance) or $\lambda_{\min}(H)\ge b$ with $b\ge1/\mathrm{poly}(n)$, for $H$ a sum of unweighted copies of $h^{(9)}_{\mathrm{ff}}$ on pairwise distinct ordered 9-tuples.
--
--   Frustration-freeness of a single-interaction Hamiltonian is therefore QMA-hard to decide.
--
--   Differences from the source:
--   - encoding: X-complete, with poly(n) bit lengths and an inverse-polynomial gap → membership for every exponent c and X-hardness for some c of the problem at exponent c; reason: the published theorem_60 convention; hardness at c implies hardness at every c′ ≥ c because the valid sets grow
--   - reading: QMA (Definition 2, p.16; an adapted, equivalent form by Remark 1) → the published InQMA / QMAHard: uniform polynomial-size {H, T, CNOT} verifiers, completeness 2/3, soundness 1/3, polynomial-time many-one reductions; reason: the base mission’s declared reading of Definition 2 (Remark 1 calls it equivalent to the standard class)
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Theorem 80, p.96

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_onCodes
import Definitions.Def_SingleInteraction_EntriesPolyTime
import Definitions.Def_SingleInteraction_Supplement_Variants

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding
open scoped ComplexOrder

namespace SingleInteraction

namespace Supplement

/-- Theorem 80 (Frustration-free SIH) (Hecker, *The Complexity of Single-Interaction Hamiltonians*,
arXiv:2609.39592 (held version, sha256 19ddc444…), §9.2, p.96): "There exists a fixed 9-local
positive-semidefinite interaction `h(9)ff` such that FF-SIH9 is QMA-complete."

There is a positive-semidefinite 9-qubit interaction `h_ff` with polynomial-time computable entries such
that FF-`SIH_9` with interaction `h_ff` (Definition 39: input `(n, L, b)` with `b ≥ 1/poly(n)`; YES:
`λmin(H) = 0`; NO: `λmin(H) ≥ b`) is in QMA for every exponent `c` and QMA-hard for some `c`.

**Formalization Note** FF-`SIH` is `ffSihProblem` (`b` of at most `(n+1)^c` bits, `b ≥ 1/(n+1)^c`).
`Matrix.PosSemidef` includes Hermitian. QMA notions as in the published `theorem_60`, through the
FF-instance codec: membership for every `c`, hardness for some `c`. -/
theorem theorem_80 :
    ∃ h : Matrix (Fin 9 → Fin 2) (Fin 9 → Fin 2) ℂ, h.PosSemidef ∧ EntriesPolyTime h ∧
      (∀ c : ℕ, InQMA (onCodes ffCodec (ffSihProblem 9 h c))) ∧
        ∃ c : ℕ, QMAHard ffCodec.encode (ffSihProblem 9 h c) := by sorry

end Supplement

end SingleInteraction
