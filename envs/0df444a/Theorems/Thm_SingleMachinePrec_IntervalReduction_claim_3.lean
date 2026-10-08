-- Prove2me | Theorems.Thm_SingleMachinePrec_IntervalReduction_claim_3
-- name    : SingleMachinePrec.IntervalReduction.claim_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:31:49.80098+00:00
-- url     : https://prove2.me/theorems/a39872be-56c4-4c80-957e-be4c2b800f00
-- title:
--   Claim 3 — the subgraph of $G^S_I$ induced by $D$ is isomorphic to $G'$
-- statement:
--   Let $G$ be a graph with a tree layout $T$, let $G'$ be the gadget graph of Stage 1, and let $S$ be the Stage 2 instance with interval order $I$. Let $G'_I=(D,E_I)$ be the subgraph of the vertex cover graph $G^S_I$ induced by the incomparable pairs in $D$. Then
--   $$G'_I \cong G'.$$
--
--   The paper's isomorphism sends $(s_i,s_j)\mapsto v_j$ (including $(s_0,s_1)\mapsto v_1$), $(s_i,m_i)\mapsto u^i_1$, $(m_i,e_i)\mapsto u^i_2$, $(s_i,b_{ij})\mapsto e^{ij}_1$ and $(b_{ij},m_j)\mapsto e^{ij}_2$. Together with Claim 1, this is what lets the weighted vertex cover problem on $G^S_I$ encode the unweighted one on $G$.
--
--   **Formalization Note** The statement asserts that a graph isomorphism exists. It does not involve the processing times, weights or $k$: the graph $G^S_I$ depends only on $I$.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 663, Claim 3 (proof pp. 663–664)

import Mathlib
import Definitions.Def_SingleMachinePrec_IntervalReduction_TreeLayout
import Definitions.Def_SingleMachinePrec_IntervalReduction_Instance

namespace SingleMachinePrec.IntervalReduction

/-- Claim 3 (p. 663): the subgraph `G′_I = (D, E_I)` of `G^S_I` induced by `D` is isomorphic
to `G′`. -/
theorem claim_3 {N : ℕ} {G : SimpleGraph (Fin N)} (L : TreeLayout G) :
    Nonempty (GIprime L ≃g GPrime L) := by sorry

end SingleMachinePrec.IntervalReduction
