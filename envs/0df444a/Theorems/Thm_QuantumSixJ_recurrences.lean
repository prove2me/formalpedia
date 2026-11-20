-- Prove2me | Theorems.Thm_QuantumSixJ_recurrences
-- name    : QuantumSixJ.recurrences
-- status  : Proved
-- author  : @igor.kh
-- created : 2026-11-13T00:17:41.031536+00:00
-- url     : https://prove2.me/theorems/cd585ab6-735a-4d43-887f-3c8290b307c7
-- title:
--   Eq. (24): Appendix-sum and categorical Tet recurrences
-- statement:
--   The theorem `QuantumSixJ.recurrences` asserts exactly `SumRecurrence ∧ NetworkRecurrence`: the conjunction of the two separately defined propositions for equation (24). The graphical Tet is defined in equation (6).
--
--   For fixed external labels, $L=(L_{jk})$ denotes the symmetric tridiagonal matrix, with $L_{jk}=L_{kj}$ and $L_{jk}=0$ unless $k\in\{j-2,j,j+2\}$. Its entries are indexed on a fixed parity lattice; $L_{00}=0$. In Lean, `QuantumSixJ.L a b c d j k` is the two-index matrix entry $L_{jk}$. The off-diagonal formulas give $L_{j,j+2}=L_{j+2,j}$, including zero extensions; symmetry is not an extra hypothesis.
--
--   1. **`SumRecurrence`: Appendix sum.** For every $a,b,c,d,j,l\in\mathbb Z$, the explicit finite Appendix sum, normalized by $h_j$, satisfies
--   $$L_{j,j-2} U_{j-2,l}+(L_{jj}-\Lambda(a,b,l)h_j)U_{jl}+L_{j,j+2} U_{j+2,l}=0.$$
--   Here $U_{jl}=\operatorname{Tet}(a,b,c,d;j,l)/h_j$ in $\mathbb Q(q)$, with the published zero extensions and no additional hypotheses. Equivalently, $L U_l=\Lambda(a,b,l)\operatorname{diag}(h_j)U_l$, displaying the symmetric generalized eigenvalue problem.
--
--   2. **`NetworkRecurrence`: categorical network.** In every $\mathbb C(q)$-linear preadditive monoidal category with additive, linear tensor product, labeled self-dual objects and trivalent vertices satisfying `SuQ2Axioms`, `VertexNormalized`, and the separate initial-data assumption `TetSeed`, for every $a,b,c,d\in\mathbb N$ and $j,l\in\mathbb Z$,
--   $$\frac{\iota(L_{j,j-2})}{\iota(h_{j-2})}T_{j-2,l}+\frac{\iota(L_{jj}-\Lambda(a,b,l)h_j)}{\iota(h_j)}T_{jl}+\frac{\iota(L_{j,j+2})}{\iota(h_{j+2})}T_{j+2,l}=0.$$
--   The coefficients act on endomorphisms of the tensor unit. The graphical network of equation (6) is $T(a,b,c,d;j,l)=X(a,d,c,b;j)\mathbin{\gg}H^R(a,d,c,b;l)$ when both channels are nonnegative and zero otherwise, with composition read left to right. The last channel is the inner rung.
--
--   The category assumptions are scalar endomorphisms of each label object, vanishing morphisms between different labels, the fusion decompositions and loop values. Vertex normalization requires only theta evaluation and cyclicity. The separate assumption `TetSeed` supplies the last-slot-2 Tet values as initial data for the recurrence solution and as input to its derivation. No second numerical Tet evaluation, general rotation, or all-channel equality between the network and Appendix sum is assumed. In both clauses field division by zero is zero; complex specialization is not part of the statement. The scalar clause is independent of all categorical hypotheses.
--
--   The scalar Tet is defined by `QuantumSixJ.tetSum`, and the graphical Tet by `QuantumSixJ.Network.Vertex.tet`. Both recurrence assertions are part of the conclusion, not hypotheses.
-- source:
--   I. Khavkine, Recurrence relation for the 6j-symbol of su_q(2) as a symmetric eigenvalue problem, International Journal of Geometric Methods in Modern Physics (2015); https://doi.org/10.1142/S0219887815501170; https://arxiv.org/abs/1009.2261. Eq. (24), both recurrence statements; Eq. (6), graphical Tet. Diagrammatic notation: Kauffman–Lins (1994). Category properties: Etingof–Ostrik, https://arxiv.org/abs/math/0302130, §2; Chen, https://arxiv.org/abs/1502.06845.

import Definitions.Def_QuantumSixJRecurrences

namespace QuantumSixJ

/-- Equation (24), for the Appendix sum and the graphical network of equation (6). -/
theorem recurrences.{v, u} : SumRecurrence ∧ NetworkRecurrence.{v, u} := by sorry

end QuantumSixJ
