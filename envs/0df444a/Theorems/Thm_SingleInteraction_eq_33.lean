-- Prove2me | Theorems.Thm_SingleInteraction_eq_33
-- name    : SingleInteraction.eq_33
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:57:33.185434+00:00
-- url     : https://prove2.me/theorems/60fe0a1d-6348-4be5-b311-4ac0f83307f9
-- title:
--   Eq. (33) — incorrect core sectors have $\lambda_{\min}\ge4S-12MR$
-- statement:
--   For every gadget and every core configuration $z$ other than the two valid ones $|0\rangle^{\otimes S}_{\mathcal A}|1\rangle^{\otimes S}_{\mathcal B}$ and $|1\rangle^{\otimes S}_{\mathcal A}|0\rangle^{\otimes S}_{\mathcal B}$,
--
--   $$\lambda_{\min}\bigl(H_{\mathrm{sim}}|_z\bigr)\ \ge\ 4S-12MR.$$
--
--   In an incorrect sector the unperturbed energy is at least $4S$, and $\|V\|\le12MR$.
--
--   Differences from the source:
--   - encoding: operators restricted to a core sector $z$ (the valid ones and, in this item, the incorrect ones) → the compression $\iota_z^\dagger(\cdot)\iota_z$ by the isometry inserting the core bits $z$, an operator on the work and mediator qubits; reason: the core configuration is conserved, so the restriction to the sector is this compression
--   - encoding: $\lambda_{\min}(\cdot)$, the ground energy → `SYKEdge.lamMin`, the infimum of $\mathrm{Re}\langle v,Av\rangle$ over unit vectors (published in `SYKEdge_MatrixNorms`); reason: the operators are Hermitian on a nonzero space, where this is the least eigenvalue
--   - reading: a construction with anchor sets $\Gamma(c)$ of $L$ distinct qubits of the mediator's register, sharing allowed, otherwise unspecified → every gadget: all $n, M, S, R, L$ with $R, L\ge 1$, $S\ge L$, all occurrence lists with $u_e\ne v_e$ and all anchor sets with $|\Gamma(c)|=L$; reason: the paper fixes no particular choice and its argument uses only $|\Gamma(c)|=L$
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.59, eq. (33)

import Mathlib
import Definitions.Def_SingleInteraction_Gadget
import Definitions.Def_SingleInteraction_Gadget_Hsim
import Definitions.Def_SingleInteraction_Gadget_comp
import Definitions.Def_SYKEdge_MatrixNorms

namespace SingleInteraction

/-- Eq. (33) (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.59): "In any incorrect core sector, the unperturbed energy increases by at
least `4S`. Hence, `λmin (Hsim|incorrect) ≥ 4S − 12MR`."

For every core configuration `z` other than the two valid ones `|0⟩^{⊗S}_𝒜 |1⟩^{⊗S}_ℬ` and
`|1⟩^{⊗S}_𝒜 |0⟩^{⊗S}_ℬ`, the ground energy of `H_sim` restricted to the sector `z` is at least `4S − 12MR`.

**Formalization Note** The restriction is the compression `ι_z† H_sim ι_z`; that it is the block of `H_sim`
on the sector (core `Z`s commute with `Ĥ`) is not assumed. The bound is real and may be negative.
`SYKEdge.lamMin` is the infimum of `re ⟨v, A v⟩` over unit vectors, the least eigenvalue of a Hermitian `A`.
For every gadget. -/
theorem eq_33 (G : Gadget) (z : G.CoreConfig) (hz : z ≠ G.zval) (hz' : z ≠ G.zval') :
    4 * (G.S : ℝ) - 12 * (G.M : ℝ) * (G.R : ℝ) ≤ SYKEdge.lamMin (G.comp z G.Hsim) := by sorry

end SingleInteraction
