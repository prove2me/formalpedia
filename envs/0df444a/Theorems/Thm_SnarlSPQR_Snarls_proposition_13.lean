-- Prove2me | Theorems.Thm_SnarlSPQR_Snarls_proposition_13
-- name    : SnarlSPQR.Snarls.proposition_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:30:39.193438+00:00
-- url     : https://prove2.me/theorems/0b7d1662-ca42-44bf-aa90-12ea855d5362
-- title:
--   Proposition 13 — the shape of a snarl on an edge {u, v} that is not a separation pair
-- statement:
--   Let $G$ be a loopless bidirected graph, $F$ a sign-cut graph of $G$, $H$ a block of $F$ containing $u$ and $v$, and let $\{u\alpha,v\beta\}$ be a snarl of $F$. Suppose that $u$ and $v$ are non-tips in $H$, that $\{u,v\}$ is an edge of $H$ (of $U(H)$), and that $\{u,v\}$ is not a separation pair of $H$. Then one of the following holds:
--   - $e=\{u\alpha,v\beta\}\in E(H)$, and every other edge of $H$ at $u$ is incident to $u$ with sign $\hat\alpha$ and every other edge at $v$ is incident to $v$ with sign $\hat\beta$;
--   - $e=\{u\hat\alpha,v\hat\beta\}\in E(H)$, and every other edge of $H$ at $u$ has sign $\alpha$ there and every other edge at $v$ has sign $\beta$ there.
--
--   Differences from the source:
--   - reading: G a bidirected graph → G : BiGraph V with G.Valid (every endpoint of an edge is a vertex, no loops); the edges form a Finset, so there are no parallel edges; reason: standing assumptions of §3 (no parallel edges, p. 9) and §5.1 (no loops, p. 28); splitting is only defined for loopless graphs
--   - reading: all vertex-sides of H at u and v except for those in e have signs α̂ and β̂ → every edge f ≠ e of H containing (u, γ) has γ = α̂, and likewise at v with β̂; reason: vertex-sides are counted per edge occurrence; read as a set of sides the clause would be empty (u has only the two sides uα, uα̂)
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), p. 38, Proposition 13

import Mathlib
import Definitions.Def_SnarlSPQR_Snarls_SignCut

namespace SnarlSPQR.Snarls

/-- Proposition 13 (p. 38): for a snarl `{uα, vβ}` of the sign-cut graph `F`, with `u, v` non-tips
of the block `H` of `F`, `{u, v}` an edge of `H` and not a separation pair of `H`: either
`e = {uα, vβ} ∈ E(H)` and every other edge of `H` at `u` (at `v`) meets it with sign `α̂` (`β̂`), or
`e = {uα̂, vβ̂} ∈ E(H)` and every other edge of `H` at `u` (at `v`) meets it with sign `α` (`β`). -/
theorem proposition_13 {V : Type} (G F H : BiGraph V) (hG : G.Valid) (hF : G.IsSignCut F)
    (hH : F.IsBlock H) (u v : V) (hu : u ∈ H.verts) (hv : v ∈ H.verts) (α β : Sign)
    (hsn : F.Snarl (u, α) (v, β)) (hut : ¬ H.IsTip u) (hvt : ¬ H.IsTip v)
    (hedge : H.U.HasEdge u v) (hsep : ¬ H.U.IsSepPair u v) :
    (s((u, α), (v, β)) ∈ H.edges ∧
      (∀ f ∈ H.edges, f ≠ s((u, α), (v, β)) → ∀ γ, (u, γ) ∈ f → γ = α.opp) ∧
      (∀ f ∈ H.edges, f ≠ s((u, α), (v, β)) → ∀ γ, (v, γ) ∈ f → γ = β.opp)) ∨
    (s((u, α.opp), (v, β.opp)) ∈ H.edges ∧
      (∀ f ∈ H.edges, f ≠ s((u, α.opp), (v, β.opp)) → ∀ γ, (u, γ) ∈ f → γ = α) ∧
      (∀ f ∈ H.edges, f ≠ s((u, α.opp), (v, β.opp)) → ∀ γ, (v, γ) ∈ f → γ = β)) := by sorry

end SnarlSPQR.Snarls
