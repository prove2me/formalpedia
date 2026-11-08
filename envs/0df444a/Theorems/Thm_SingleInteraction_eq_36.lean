-- Prove2me | Theorems.Thm_SingleInteraction_eq_36
-- name    : SingleInteraction.eq_36
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:34.687731+00:00
-- url     : https://prove2.me/theorems/8e8be5a9-5982-44e5-9de9-552f5eb29b46
-- title:
--   Eq. (36) — $-\eta QH_0Q\preceq QVQ\preceq\eta QH_0Q$
-- statement:
--   For every gadget, in the chosen valid core sector, with $\eta=(1+2\sqrt{MR})/L$,
--
--   $$-\eta\,QH_0Q\ \preceq\ QVQ\ \preceq\ \eta\,QH_0Q.$$
--
--   The perturbation is small relative to the unperturbed energy on the excited subspace, although $\|V\|$ itself is of order $MR$, far above the gap $4L$. No assumption on $\eta$ is needed.
--
--   Differences from the source:
--   - encoding: operators restricted to the chosen valid core sector $|0\rangle^{\otimes S}_{\mathcal A}|1\rangle^{\otimes S}_{\mathcal B}$, "understood as acting on the work and mediator registers" → the compression $\iota_z^\dagger(\cdot)\iota_z$ by the isometry inserting the core bits $z$, an operator on the work and mediator qubits; reason: the core configuration is conserved, so the restriction to the sector is this compression
--   - encoding: $A\preceq B$ → $B-A$ positive semidefinite (`Matrix.PosSemidef`); reason: the definition of the Loewner order
--   - reading: a construction with anchor sets $\Gamma(c)$ of $L$ distinct qubits of the mediator's register, sharing allowed, otherwise unspecified → every gadget: all $n, M, S, R, L$ with $R, L\ge 1$, $S\ge L$, all occurrence lists with $u_e\ne v_e$ and all anchor sets with $|\Gamma(c)|=L$; reason: the paper fixes no particular choice and its argument uses only $|\Gamma(c)|=L$
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.5, p.62, eq. (36)

import Mathlib
import Definitions.Def_SingleInteraction_Gadget
import Definitions.Def_SingleInteraction_Gadget_Pzero
import Definitions.Def_SingleInteraction_Gadget_H2eff
import Definitions.Def_SingleInteraction_Gadget_epsEff

open scoped ComplexOrder

namespace SingleInteraction

/-- Eq. (36) (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.5, p.62): "Since this bound holds for every normalized state in `Q`, it
establishes the relative operator inequality `−ηQH0Q ⪯ QV Q ⪯ ηQH0Q`", with `η = (1 + 2√(MR))/L`.

**Formalization Note** In the chosen valid core sector; `A ⪯ B` is `(B − A).PosSemidef`. No assumption on
`η`. For every gadget. -/
theorem eq_36 (G : Gadget) :
    (((G.eta : ℝ) : ℂ) • (G.Qexc * G.H0v * G.Qexc) - G.Qexc * G.Vv * G.Qexc).PosSemidef ∧
      (G.Qexc * G.Vv * G.Qexc + ((G.eta : ℝ) : ℂ) • (G.Qexc * G.H0v * G.Qexc)).PosSemidef := by sorry

end SingleInteraction
