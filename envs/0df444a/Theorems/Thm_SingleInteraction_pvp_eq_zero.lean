-- Prove2me | Theorems.Thm_SingleInteraction_pvp_eq_zero
-- name    : SingleInteraction.pvp_eq_zero
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:51.365864+00:00
-- url     : https://prove2.me/theorems/8f47f0c7-8173-4319-b513-27ceeb9b1175
-- title:
--   §5.1.3 — $PVP=0$, so the valid-sector ground energy is at most $0$
-- statement:
--   For every gadget, in the chosen valid core sector,
--
--   $$PVP=0,$$
--
--   and consequently $\lambda_{\min}(H_{\mathrm{sim}})\le0$ there. The diagonal parts of $V$ cancel on the zero-defect subspace because each occurrence has equally many mediators anchored to $\mathcal A$ and to $\mathcal B$, and the exchange parts have no matrix elements inside it.
--
--   Differences from the source:
--   - encoding: operators restricted to the chosen valid core sector $|0\rangle^{\otimes S}_{\mathcal A}|1\rangle^{\otimes S}_{\mathcal B}$, "understood as acting on the work and mediator registers" → the compression $\iota_z^\dagger(\cdot)\iota_z$ by the isometry inserting the core bits $z$, an operator on the work and mediator qubits; reason: the core configuration is conserved, so the restriction to the sector is this compression
--   - encoding: $\lambda_{\min}(\cdot)$, the ground energy → `SYKEdge.lamMin`, the infimum of $\mathrm{Re}\langle v,Av\rangle$ over unit vectors (published in `SYKEdge_MatrixNorms`); reason: the operators are Hermitian on a nonzero space, where this is the least eigenvalue
--   - reading: a construction with anchor sets $\Gamma(c)$ of $L$ distinct qubits of the mediator's register, sharing allowed, otherwise unspecified → every gadget: all $n, M, S, R, L$ with $R, L\ge 1$, $S\ge L$, all occurrence lists with $u_e\ne v_e$ and all anchor sets with $|\Gamma(c)|=L$; reason: the paper fixes no particular choice and its argument uses only $|\Gamma(c)|=L$
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.59

import Mathlib
import Definitions.Def_SingleInteraction_Gadget
import Definitions.Def_SingleInteraction_Gadget_Pzero
import Definitions.Def_SingleInteraction_Gadget_H2eff
import Definitions.Def_SYKEdge_MatrixNorms

namespace SingleInteraction

/-- `PVP = 0` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.59): "the equal numbers of mediators anchored to `𝒜` and `ℬ` imply that
their diagonal contributions to `V` cancel within the zero-defect subspace. The exchange terms have
vanishing matrix elements within this subspace. Therefore, `PV P = 0`. It follows that the ground energy
of `Hsim` in this valid core sector is at most zero."

**Formalization Note** In the chosen valid core sector `|0⟩^{⊗S}_𝒜 |1⟩^{⊗S}_ℬ` (`Vv`, `Hsimv`); ground
energy is the minimum of `⟨ϕ|·|ϕ⟩` over unit vectors. For every gadget. -/
theorem pvp_eq_zero (G : Gadget) :
    G.Pzero * G.Vv * G.Pzero = 0 ∧ SYKEdge.lamMin G.Hsimv ≤ 0 := by sorry

end SingleInteraction
