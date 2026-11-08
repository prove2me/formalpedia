-- Prove2me | Theorems.Thm_SingleInteraction_eq_32
-- name    : SingleInteraction.eq_32
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:40.061298+00:00
-- url     : https://prove2.me/theorems/0347a127-ee0f-4e34-8284-f6aad365ee29
-- title:
--   Eq. (32) — $H_0=4L\mathcal N$, $PH_0P=0$, $QH_0Q\succeq4LQ$
-- statement:
--   For every gadget, in the chosen valid core sector $|0\rangle^{\otimes S}_{\mathcal A}|1\rangle^{\otimes S}_{\mathcal B}$ (on the work and mediator registers),
--
--   $$H_0=4L\,\mathcal N,\qquad PH_0P=0,\qquad QH_0Q\succeq4L\,Q.$$
--
--   Every mediator defect costs exactly $4L$; this gap of the unperturbed Hamiltonian is what the perturbative analysis of §5.1.4–5.1.6 rests on.
--
--   Differences from the source:
--   - encoding: operators restricted to the chosen valid core sector $|0\rangle^{\otimes S}_{\mathcal A}|1\rangle^{\otimes S}_{\mathcal B}$, "understood as acting on the work and mediator registers" → the compression $\iota_z^\dagger(\cdot)\iota_z$ by the isometry inserting the core bits $z$, an operator on the work and mediator qubits; reason: the core configuration is conserved, so the restriction to the sector is this compression
--   - encoding: $A\preceq B$ → $B-A$ positive semidefinite (`Matrix.PosSemidef`); reason: the definition of the Loewner order
--   - reading: a construction with anchor sets $\Gamma(c)$ of $L$ distinct qubits of the mediator's register, sharing allowed, otherwise unspecified → every gadget: all $n, M, S, R, L$ with $R, L\ge 1$, $S\ge L$, all occurrence lists with $u_e\ne v_e$ and all anchor sets with $|\Gamma(c)|=L$; reason: the paper fixes no particular choice and its argument uses only $|\Gamma(c)|=L$
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.59, display above (32) and eq. (32)

import Mathlib
import Definitions.Def_SingleInteraction_Gadget
import Definitions.Def_SingleInteraction_Gadget_Pzero
import Definitions.Def_SingleInteraction_Gadget_H2eff

open scoped ComplexOrder

namespace SingleInteraction

/-- `H0 = 4L𝒩` and eq. (32) (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.59): within the chosen valid core sector
`|0⟩^{⊗S}_𝒜 |1⟩^{⊗S}_ℬ`, "every mediator defect contributes an energy of `4L`, so `H0 = 4L𝒩`", and
"`PH0P = 0`, `QH0Q ⪰ 4LQ`".

**Formalization Note** `H0v` is `ι_z† H0 ι_z` for `z = |0⟩^{⊗S}_𝒜 |1⟩^{⊗S}_ℬ`, an operator on the work and
mediator qubits; `⪰` is `Matrix.PosSemidef` of the difference. The statement holds for every gadget
(all `n, M, S, R, L`, occurrences and anchor sets with `|Γ(c)| = L`, `R, L ≥ 1`, `S ≥ L`). -/
theorem eq_32 (G : Gadget) :
    G.H0v = (4 * (G.L : ℂ)) • G.Ncount ∧ G.Pzero * G.H0v * G.Pzero = 0 ∧
      (G.Qexc * G.H0v * G.Qexc - (4 * (G.L : ℂ)) • G.Qexc).PosSemidef := by sorry

end SingleInteraction
