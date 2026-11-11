-- Prove2me | Theorems.Thm_SnarlSPQR_Snarls_proposition_9
-- name    : SnarlSPQR.Snarls.proposition_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:31:09.585142+00:00
-- url     : https://prove2.me/theorems/8e7bec0d-9834-42e0-9e73-03ffeb85e3be
-- title:
--   Proposition 9 — consecutive good vertices of an S-node form snarls
-- statement:
--   Let $G$ be a loopless bidirected graph, $H$ a maximal 2-connected subgraph of $G$, $T$ an SPQR tree of $H$ (Q-nodes omitted) and $\mu$ an S-node of $T$. Label $\mathrm{skeleton}(\mu)$ cyclically by vertices $v_0,\dots,v_{k-1}$ and edges $e_0,\dots,e_{k-1}$, where $e_i$ has endpoints $v_i$ and $v_{(i+1)\bmod k}$ and $k\ge3$. For a good vertex $v_i$, write $\hat\alpha_i$ for the sign of the vertex-sides at $v_i$ in $\mathrm{expansion}(e_{(i-1)\bmod k})$ and $\alpha_i$ for the sign in $\mathrm{expansion}(e_i)$.
--
--   Let $v_{i_1},\dots,v_{i_q}$ be the good vertices, with $q\ge2$ and $i_1<\dots<i_q$. Then the $q$ pairs
--   $$\{v_{i_1}\alpha_{i_1},\,v_{i_2}\hat\alpha_{i_2}\},\ \dots,\ \{v_{i_q}\alpha_{i_q},\,v_{i_1}\hat\alpha_{i_1}\}$$
--   are snarls of $G$.
--
--   In Lean: for good $v_i\neq v_j$ such that $v_j$ is the next good vertex after $v_i$ in the cyclic order, $\{v_i\alpha_i, v_j\hat\alpha_j\}$ is a snarl. This covers each of the $q$ pairs.
--
--   Differences from the source:
--   - reading: G a bidirected graph → G : BiGraph V with G.Valid (every endpoint of an edge is a vertex, no loops); the edges form a Finset, so there are no parallel edges; reason: standing assumptions of §3 (no parallel edges, p. 9) and §5.1 (no loops, p. 28); splitting is only defined for loopless graphs
--   - reading: T the SPQR tree of H (Q-nodes omitted) → T any tree with H.U.IsSPQRTree e T, for any reference edge e ∈ E(H); nodes are the non-Q subtrees; reason: the recursive definition (pp. 6–8) depends on a reference edge and lists children in no fixed order; the statement is claimed for the SPQR tree whichever is chosen
--   - encoding: the good vertices v_{i_1}, …, v_{i_q} with q ≥ 2 and the q cyclically consecutive pairs → one statement per pair: good i ≠ j with no good index strictly between i and j in the cyclic order (i → j); q ≥ 2 is implied by i ≠ j; reason: the conclusion is a list of q snarls, one per cyclically consecutive pair of good vertices
--   - encoding: skeleton(μ) has vertices v_0..v_{k−1} and edges e_0..e_{k−1} → IsCycleLabel μ k v σ: injective vertex map onto the skeleton vertices, bijection σ onto the slots, slot σ i with endpoints {v i, v ((i+1) % k)}; reason: indices as natural numbers below k
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), p. 35, Proposition 9

import Mathlib
import Definitions.Def_SnarlSPQR_Snarls_GoodVertex

namespace SnarlSPQR.Snarls

/-- Proposition 9 (p. 35): for an S-node `μ` with cyclic labelling `v₀, …, v_{k−1}`,
`e₀, …, e_{k−1}` (`e_i = {v_i, v_{(i+1) mod k}}`, `k ≥ 3`), and two good vertices `v_i ≠ v_j` such
that `v_j` is the next good vertex after `v_i` in the cyclic order, `{v_i α_i, v_j α̂_j}` is a snarl,
where `α_i` is the sign at `v_i` in `expansion(e_i)` and `α̂_j` the sign at `v_j` in
`expansion(e_{(j−1) mod k})`. (Ranging over all such consecutive pairs gives the `q ≥ 2` snarls
`{v_{i₁} α_{i₁}, v_{i₂} α̂_{i₂}}, …, {v_{i_q} α_{i_q}, v_{i₁} α̂_{i₁}}`.) -/
theorem proposition_9 {V : Type} (G H : BiGraph V) (hG : G.Valid) (hH : G.IsMax2Conn H)
    (e : Sym2 (V × Sign)) (T : Tree V (Sym2 (V × Sign))) (hT : H.U.IsSPQRTree e T)
    (μ : Tree V (Sym2 (V × Sign))) (hμ : T.IsNode μ) (hS : μ.kind? = some .S)
    (k : ℕ) (v : ℕ → V) (σ : ℕ → ℕ) (hlab : BiGraph.IsCycleLabel μ k v σ) (hk : 3 ≤ k)
    (i j : ℕ) (hik : i < k) (hjk : j < k) (hij : i ≠ j) (α β : Sign)
    (hi : G.GoodWith H e T μ k v σ i α) (hj : G.GoodWith H e T μ k v σ j β)
    (hnext : ∀ l < k, G.IsGood H e T μ k v σ l →
      ¬ ((i < j ∧ i < l ∧ l < j) ∨ (j < i ∧ (i < l ∨ l < j)))) :
    G.Snarl (v i, α) (v j, β.opp) := by sorry

end SnarlSPQR.Snarls
