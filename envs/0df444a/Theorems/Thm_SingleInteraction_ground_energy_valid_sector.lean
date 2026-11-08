-- Prove2me | Theorems.Thm_SingleInteraction_ground_energy_valid_sector
-- name    : SingleInteraction.ground_energy_valid_sector
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:38.876604+00:00
-- url     : https://prove2.me/theorems/36b30a2d-03dd-4410-b0e6-07cc5ac8121b
-- title:
--   §5.1.3 — for $S>3MR$ the ground energy of $H_{\mathrm{sim}}$ is that of the chosen valid sector
-- statement:
--   For every gadget:
--
--   1. the two valid core sectors have the same ground energy;
--   2. if $S>3MR$, every incorrect core sector has ground energy strictly larger than that of the chosen valid sector, and
--
--   $$\lambda_{\min}(H_{\mathrm{sim}})=\lambda_{\min}\bigl(H_{\mathrm{sim}}|_{|0\rangle^{\otimes S}_{\mathcal A}|1\rangle^{\otimes S}_{\mathcal B}}\bigr).$$
--
--   This reduces the spectral analysis of the full gadget to the chosen valid sector.
--
--   Differences from the source:
--   - encoding: operators restricted to a core sector $z$ (the valid ones and, in this item, the incorrect ones) → the compression $\iota_z^\dagger(\cdot)\iota_z$ by the isometry inserting the core bits $z$, an operator on the work and mediator qubits; reason: the core configuration is conserved, so the restriction to the sector is this compression
--   - encoding: $\lambda_{\min}(\cdot)$, the ground energy → `SYKEdge.lamMin`, the infimum of $\mathrm{Re}\langle v,Av\rangle$ over unit vectors (published in `SYKEdge_MatrixNorms`); reason: the operators are Hermitian on a nonzero space, where this is the least eigenvalue
--   - reading: a construction with anchor sets $\Gamma(c)$ of $L$ distinct qubits of the mediator's register, sharing allowed, otherwise unspecified → every gadget: all $n, M, S, R, L$ with $R, L\ge 1$, $S\ge L$, all occurrence lists with $u_e\ne v_e$ and all anchor sets with $|\Gamma(c)|=L$; reason: the paper fixes no particular choice and its argument uses only $|\Gamma(c)|=L$
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.59

import Mathlib
import Definitions.Def_SingleInteraction_Gadget
import Definitions.Def_SingleInteraction_Gadget_Hsim
import Definitions.Def_SingleInteraction_Gadget_comp
import Definitions.Def_SingleInteraction_Gadget_H2eff
import Definitions.Def_SYKEdge_MatrixNorms

namespace SingleInteraction

/-- The valid-sector reduction (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.59): "Choosing `S > 3MR` makes this lower bound strictly
positive. Since a valid core sector has ground energy at most zero, no incorrect core sector can contain a
global ground state. Since all incorrect core sectors have higher ground-state energies, and the two valid
core sectors have the same ground-state energy, the ground energy of `Hsim` equals its ground energy in the
chosen valid core sector."

1. the two valid core sectors have the same ground energy;
2. if `S > 3MR`, every incorrect core sector has ground energy strictly above that of the chosen valid
   sector, and the ground energy of `H_sim` on all physical qubits equals its ground energy in the chosen
   valid sector `|0⟩^{⊗S}_𝒜 |1⟩^{⊗S}_ℬ`.

**Formalization Note** Sector restrictions are the compressions `ι_z† H_sim ι_z`. For every gadget. -/
theorem ground_energy_valid_sector (G : Gadget) :
    SYKEdge.lamMin (G.comp G.zval' G.Hsim) = SYKEdge.lamMin G.Hsimv ∧
      (3 * G.M * G.R < G.S →
        (∀ z : G.CoreConfig, z ≠ G.zval → z ≠ G.zval' →
            SYKEdge.lamMin G.Hsimv < SYKEdge.lamMin (G.comp z G.Hsim)) ∧
          SYKEdge.lamMin G.Hsim = SYKEdge.lamMin G.Hsimv) := by sorry

end SingleInteraction
