-- Prove2me | Theorems.Thm_SingleInteraction_eq_35
-- name    : SingleInteraction.eq_35
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:59:07.176659+00:00
-- url     : https://prove2.me/theorems/8ef77321-4784-4eff-8080-20d80692d24f
-- title:
--   Eq. (35) — $H^{(2)}_{\mathrm{eff}}=\frac RL(K-2MI)$
-- statement:
--   For every gadget, in the chosen valid core sector,
--
--   $$H^{(2)}_{\mathrm{eff}}=-PVQ(QH_0Q)^{-1}QVP=\frac RL\,(K-2MI),$$
--
--   where the inverse is taken on the range of $Q$ and the right-hand side acts on the zero-defect subspace, identified with the work register. At second order the gadget reproduces the target XY occurrence Hamiltonian up to the factor $R/L$ and the shift $-2MR/L$.
--
--   Differences from the source:
--   - encoding: operators restricted to the chosen valid core sector $|0\rangle^{\otimes S}_{\mathcal A}|1\rangle^{\otimes S}_{\mathcal B}$, "understood as acting on the work and mediator registers" → the compression $\iota_z^\dagger(\cdot)\iota_z$ by the isometry inserting the core bits $z$, an operator on the work and mediator qubits; reason: the core configuration is conserved, so the restriction to the sector is this compression
--   - encoding: the inverse "taken on the range of $Q$" → `invOn Q A` $= Q\,(QAQ+(1-Q))^{-1}Q$; reason: it is the inverse of $QAQ|_{\mathrm{ran}\,Q}$ on $\mathrm{ran}\,Q$ and $0$ on its complement whenever that inverse exists, as it does here
--   - encoding: "identifying the zero-defect subspace with the work-register Hilbert space", $\frac RL(K-2MI)$ → $\frac RL\,(K P-2M\,P)$ on the work and mediator registers, with $K$ acting on the work qubits; reason: the zero-defect subspace is $\mathrm{ran}\,P$, the work register tensored with $|\Omega\rangle$; $K$ commutes with $P$
--   - reading: a construction with anchor sets $\Gamma(c)$ of $L$ distinct qubits of the mediator's register, sharing allowed, otherwise unspecified → every gadget: all $n, M, S, R, L$ with $R, L\ge 1$, $S\ge L$, all occurrence lists with $u_e\ne v_e$ and all anchor sets with $|\Gamma(c)|=L$; reason: the paper fixes no particular choice and its argument uses only $|\Gamma(c)|=L$
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.4, p.61, eq. (35)

import Mathlib
import Definitions.Def_SingleInteraction_Gadget
import Definitions.Def_SingleInteraction_Gadget_Pzero
import Definitions.Def_SingleInteraction_Gadget_Kocc
import Definitions.Def_SingleInteraction_Gadget_H2eff

namespace SingleInteraction

/-- Eq. (35) (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.4, p.61): "Substituting into the second-order expression derived above, and
identifying the zero-defect subspace with the work-register Hilbert space, we obtain
`H_eff^(2) = −PV Q(QH0Q)^{−1}QV P = (R/L)(K − 2MI)`."

**Formalization Note** In the chosen valid core sector, on the work and mediator register. The inverse is
taken on ran `Q` (`invOn`). "Identifying the zero-defect subspace with the work register" is the right-hand
side `(R/L)(K − 2M I) P`, with `K` acting on the work qubits (`Klift`); `K` commutes with `P`. For every
gadget. -/
theorem eq_35 (G : Gadget) :
    G.H2eff = ((G.R : ℂ) / (G.L : ℂ)) • (G.Klift * G.Pzero - (2 * (G.M : ℂ)) • G.Pzero) := by sorry

end SingleInteraction
