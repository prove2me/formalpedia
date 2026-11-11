-- Prove2me | Theorems.Thm_SnarlSPQR_Snarls_proposition_10
-- name    : SnarlSPQR.Snarls.proposition_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:31:04.907452+00:00
-- url     : https://prove2.me/theorems/03f248bc-35ca-4949-84b3-5c48014f6b6b
-- title:
--   Proposition 10 — characterization of separability at a P-node
-- statement:
--   Let $G$ be a loopless bidirected graph, $F$ a sign-cut graph of $G$, $H$ a maximal 2-connected subgraph of $F$, and $T$ an SPQR tree of $H$ (Q-nodes omitted). Let $\mu$ be a P-node of $T$ whose skeleton has edges $e_1,\dots,e_k$, all with endpoints $\{u,v\}$, where $k\ge3$. For signs $\alpha,\beta$ let
--   $$E^\alpha_u=\{e_i : N^\alpha_{\mathrm{expansion}(e_i)}(u)\neq\emptyset\},\qquad E^\beta_v=\{e_i : N^\beta_{\mathrm{expansion}(e_i)}(v)\neq\emptyset\}.$$
--   Then $\{u\alpha,v\beta\}$ is separable in $F$ if and only if all five of the following hold:
--   - $E^\alpha_u\neq\emptyset$;
--   - $E^\alpha_u\cap E^{\hat\alpha}_u=\emptyset$;
--   - $E^\beta_v\cap E^{\hat\beta}_v=\emptyset$;
--   - $E^\alpha_u=E^\beta_v$;
--   - neither $u$ nor $v$ has a dangling block with respect to $H$ (blocks of $F$).
--
--   Differences from the source:
--   - reading: G a bidirected graph → G : BiGraph V with G.Valid (every endpoint of an edge is a vertex, no loops); the edges form a Finset, so there are no parallel edges; reason: standing assumptions of §3 (no parallel edges, p. 9) and §5.1 (no loops, p. 28); splitting is only defined for loopless graphs
--   - reading: T the SPQR tree of H (Q-nodes omitted) → T any tree with H.U.IsSPQRTree e T, for any reference edge e ∈ E(H); nodes are the non-Q subtrees; reason: the recursive definition (pp. 6–8) depends on a reference edge and lists children in no fixed order; the statement is claimed for the SPQR tree whichever is chosen
--   - encoding: E^α_u ⊆ {e_1, …, e_k} → slotsWithSide H e T μ u α: the set of slot indices i of skeleton(μ) with N^α of the expansion of slot i at u nonempty; reason: skeleton edges are identified by their slot index
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), p. 36, Proposition 10

import Mathlib
import Definitions.Def_SnarlSPQR_Snarls_GoodVertex

namespace SnarlSPQR.Snarls

/-- Proposition 10 (p. 36): for a P-node `μ` whose skeleton has `k ≥ 3` edges with endpoints
`{u, v}`, `{uα, vβ}` is separable in the sign-cut graph `F` if and only if `E^α_u ≠ ∅`,
`E^α_u ∩ E^α̂_u = ∅`, `E^β_v ∩ E^β̂_v = ∅`, `E^α_u = E^β_v`, and `u, v` have no dangling blocks
with respect to `H`. -/
theorem proposition_10 {V : Type} (G F H : BiGraph V) (hG : G.Valid) (hF : G.IsSignCut F)
    (hH : F.IsMax2Conn H)
    (e : Sym2 (V × Sign)) (T : Tree V (Sym2 (V × Sign))) (hT : H.U.IsSPQRTree e T)
    (μ : Tree V (Sym2 (V × Sign))) (hμ : T.IsNode μ) (hP : μ.kind? = some .P)
    (u v : V) (hends : ∀ p ∈ μ.slots, p = s(u, v)) (hk : 3 ≤ μ.slots.length) (α β : Sign) :
    F.Separable (u, α) (v, β) ↔
      ((H.slotsWithSide e T μ u α).Nonempty ∧
        H.slotsWithSide e T μ u α ∩ H.slotsWithSide e T μ u α.opp = ∅ ∧
        H.slotsWithSide e T μ v β ∩ H.slotsWithSide e T μ v β.opp = ∅ ∧
        H.slotsWithSide e T μ u α = H.slotsWithSide e T μ v β ∧
        ¬ F.HasDangling H u ∧ ¬ F.HasDangling H v) := by sorry

end SnarlSPQR.Snarls
