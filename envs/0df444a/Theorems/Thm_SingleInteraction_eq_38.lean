-- Prove2me | Theorems.Thm_SingleInteraction_eq_38
-- name    : SingleInteraction.eq_38
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:00:15.79621+00:00
-- url     : https://prove2.me/theorems/3a8349e7-6f3a-4ee5-80e0-7630fa65400f
-- title:
--   Eq. (38) — $|E-\frac RL(\lambda_{\min}(K)-2M)|\le\varepsilon_{\mathrm{eff}}$
-- statement:
--   For every gadget with $\eta<1$, let $E$ be the ground energy of $H_{\mathrm{sim}}$ in the chosen valid core sector and $\lambda_{\min}(K)$ the ground energy of the target XY occurrence Hamiltonian on the work qubits. Then
--
--   $$\Bigl|E-\frac RL\bigl(\lambda_{\min}(K)-2M\bigr)\Bigr|\ \le\ \varepsilon_{\mathrm{eff}}.$$
--
--   With the parameter choice (39) this transfers the promise of the XY occurrence problem to the gadget, which is the hardness half of Theorem 60.
--
--   Differences from the source:
--   - encoding: operators restricted to the chosen valid core sector $|0\rangle^{\otimes S}_{\mathcal A}|1\rangle^{\otimes S}_{\mathcal B}$, "understood as acting on the work and mediator registers" → the compression $\iota_z^\dagger(\cdot)\iota_z$ by the isometry inserting the core bits $z$, an operator on the work and mediator qubits; reason: the core configuration is conserved, so the restriction to the sector is this compression
--   - encoding: $\lambda_{\min}(\cdot)$, the ground energy → `SYKEdge.lamMin`, the infimum of $\mathrm{Re}\langle v,Av\rangle$ over unit vectors (published in `SYKEdge_MatrixNorms`); reason: the operators are Hermitian on a nonzero space, where this is the least eigenvalue
--   - reading: a construction with anchor sets $\Gamma(c)$ of $L$ distinct qubits of the mediator's register, sharing allowed, otherwise unspecified → every gadget: all $n, M, S, R, L$ with $R, L\ge 1$, $S\ge L$, all occurrence lists with $u_e\ne v_e$ and all anchor sets with $|\Gamma(c)|=L$; reason: the paper fixes no particular choice and its argument uses only $|\Gamma(c)|=L$
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.6, p.64, eq. (38); standing assumption "Assume η < 1", p.63

import Mathlib
import Definitions.Def_SingleInteraction_Gadget
import Definitions.Def_SingleInteraction_Gadget_Kocc
import Definitions.Def_SingleInteraction_Gadget_Fexact
import Definitions.Def_SingleInteraction_Gadget_epsEff
import Definitions.Def_SYKEdge_MatrixNorms

namespace SingleInteraction

/-- Eq. (38) (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.6, p.64), under the standing assumption "Assume `η < 1`" (p.63): "Finally, since
`E = λmin(F(E))`, the variational eigenvalue bound and eq. (35) imply `|E − (R/L)(λmin(K) − 2M)| ≤ ε_eff`."

Here `E` is the ground energy of `H_sim` in the chosen valid core sector and `λmin(K)` the ground energy of
the target XY occurrence Hamiltonian `K` on the `n` work qubits.

**Formalization Note** For every gadget. -/
theorem eq_38 (G : Gadget) (hη : G.eta < 1) :
    |G.Eval - (G.R : ℝ) / (G.L : ℝ) * (SYKEdge.lamMin G.Kocc - 2 * (G.M : ℝ))| ≤ G.epsEff := by sorry

end SingleInteraction
