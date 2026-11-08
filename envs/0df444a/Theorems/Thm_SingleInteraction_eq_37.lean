-- Prove2me | Theorems.Thm_SingleInteraction_eq_37
-- name    : SingleInteraction.eq_37
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:59:56.031869+00:00
-- url     : https://prove2.me/theorems/c319cbb8-17e2-4395-b935-7556a15a3629
-- title:
--   Eq. (37) — $\|F(E)-H^{(2)}_{\mathrm{eff}}\|\le\varepsilon_{\mathrm{eff}}$
-- statement:
--   For every gadget with $\eta<1$, let $E$ be the ground energy of $H_{\mathrm{sim}}$ in the chosen valid core sector. Then
--
--   $$\bigl\|F(E)-H^{(2)}_{\mathrm{eff}}\bigr\|\ \le\ \frac{4MR}{L}\left[\frac{\eta}{1-\eta}+\frac{MR}{L^2(1-\eta)^2}\right]=\varepsilon_{\mathrm{eff}},$$
--
--   in operator norm. The exact effective Hamiltonian is close to the second-order one.
--
--   Differences from the source:
--   - encoding: operators restricted to the chosen valid core sector $|0\rangle^{\otimes S}_{\mathcal A}|1\rangle^{\otimes S}_{\mathcal B}$, "understood as acting on the work and mediator registers" → the compression $\iota_z^\dagger(\cdot)\iota_z$ by the isometry inserting the core bits $z$, an operator on the work and mediator qubits; reason: the core configuration is conserved, so the restriction to the sector is this compression
--   - encoding: the inverse "taken on the range of $Q$" → `invOn Q A` $= Q\,(QAQ+(1-Q))^{-1}Q$; reason: it is the inverse of $QAQ|_{\mathrm{ran}\,Q}$ on $\mathrm{ran}\,Q$ and $0$ on its complement whenever that inverse exists, as it does here
--   - encoding: $\lambda_{\min}(\cdot)$, the ground energy → `SYKEdge.lamMin`, the infimum of $\mathrm{Re}\langle v,Av\rangle$ over unit vectors (published in `SYKEdge_MatrixNorms`); reason: the operators are Hermitian on a nonzero space, where this is the least eigenvalue
--   - reading: a construction with anchor sets $\Gamma(c)$ of $L$ distinct qubits of the mediator's register, sharing allowed, otherwise unspecified → every gadget: all $n, M, S, R, L$ with $R, L\ge 1$, $S\ge L$, all occurrence lists with $u_e\ne v_e$ and all anchor sets with $|\Gamma(c)|=L$; reason: the paper fixes no particular choice and its argument uses only $|\Gamma(c)|=L$
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.6, p.64, eq. (37); standing assumption "Assume η < 1", p.63

import Mathlib
import Definitions.Def_SingleInteraction_Gadget
import Definitions.Def_SingleInteraction_Gadget_H2eff
import Definitions.Def_SingleInteraction_Gadget_Fexact
import Definitions.Def_SingleInteraction_Gadget_epsEff
import Definitions.Def_SYKEdge_MatrixNorms

namespace SingleInteraction

/-- Eq. (37) (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.6, p.64), under the standing assumption "Assume `η < 1`" (p.63): with
`E = λmin(Hsim)` in the chosen valid core sector,
`‖F(E) − H_eff^(2)‖ ≤ (4MR/L) [η/(1 − η) + MR/(L²(1 − η)²)] =: ε_eff`.

**Formalization Note** `‖·‖` is the operator norm (`SYKEdge.opNorm`). `F(E)` and `H_eff^(2)` are operators on the
work and mediator register of the chosen valid sector, both supported on ran `P`. For every gadget. -/
theorem eq_37 (G : Gadget) (hη : G.eta < 1) :
    SYKEdge.opNorm (G.Fexact G.Eval - G.H2eff) ≤ G.epsEff := by sorry

end SingleInteraction
