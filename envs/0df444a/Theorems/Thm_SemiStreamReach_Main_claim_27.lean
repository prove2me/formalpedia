-- Prove2me | Theorems.Thm_SemiStreamReach_Main_claim_27
-- name    : SemiStreamReach.Main.claim_27
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:52:28.251025+00:00
-- url     : https://prove2.me/theorems/d339e894-f472-4051-af48-6b601b05e742
-- title:
--   Claim 27 — the block $B_p$ contains the prefix (suffix) of a short piece up to a vertex of the in-ball (out-ball) of $p$
-- statement:
--   Let $G'$ be a weighted directed graph with positive weights, $\Pi$ a set of pivots with radii $\rho_p\ge0$, $D\ge0$, and $Q=\langle v_0,\dots,v_\ell\rangle$ a path in $G'$ of length $w(Q)\le D$. For a pivot $p$, its block is $B_p=R^\pm_{\rho_p+D}(G',p)$. If $v_a$ lies in the in-ball $R^-_{\rho_p}(G',p)$ of $p$, then
--   $$v_{a'}\in B_p\qquad\text{for all } 0\le a'\le a,$$
--   and if $v_a$ lies in the out-ball $R^+_{\rho_p}(G',p)$, then $v_{a'}\in B_p$ for all $a\le a'\le\ell$.
--
--   The margin $D$ in the radius of $B_p$ is what lets one block-closure edge shortcut the whole prefix (suffix) of a piece at a late level.
--
--   Differences from the source:
--   - generalization: Q is a piece of P at a late level r in a subgraph G′ of the recursion, with sampled pivots and radii ρ_p = η_p D_r, η_p ∈ [λ, 2λ) → any graph G′ with positive weights on a finite type, any pivot set Π, any radii ρ_p ≥ 0, any D ≥ 0 and any simple path Q in G′ with w(Q) ≤ D; reason: the proof uses only w(Q) ≤ D_r, ρ_p ≥ 0 and the definitions of the balls and of B_p; the Lean statement specializes to the pieces of the paper
--   - encoding: Q[v_0, …, v_a] and Q[v_a, …, v_ℓ] → list positions Q[a'] for a' ≤ a and a ≤ a' < |Q|; reason: Lean convention; same instances
-- source:
--   Hoppenworth, Li, Mahabadi, Tarnawski, Semi-Streaming Reachability and Shortest Paths in n^{1/3+o(1)} Passes, arXiv:2611.05061 (PDF sha256 c1b64474…), p. 31 (PDF 33), Claim 27

import Mathlib
import Definitions.Def_SemiStreamReach_Main_Distances
import Definitions.Def_SemiStreamReach_Main_LateLevel

open scoped ENNReal

namespace SemiStreamReach.Main

/-- Claim 27, p. 31 (PDF 33). Let `G′` have positive weights, pivots `Π` with radii `ρ_p ≥ 0`,
scale `D ≥ 0`, and let `Q = ⟨v_0, …, v_ℓ⟩` be a path in `G′` of length `w(Q) ≤ D`. For any pivot
`p`: if `v_a` lies in the in-ball `R^−_{ρ_p}(G′, p)`, then every vertex of the prefix
`Q[v_0, …, v_a]` lies in the block `B_p = R^±_{ρ_p + D}(G′, p)`; if `v_a` lies in the out-ball
`R^+_{ρ_p}(G′, p)`, then every vertex of the suffix `Q[v_a, …, v_ℓ]` lies in `B_p`. -/
theorem claim_27 {V : Type*} [Fintype V] (G : WGraph V) (Pi : Set V) (ρ : V → ℝ) (D : ℝ)
    (Q : List V) (hG : PositiveWeights G) (hρ : ∀ p ∈ Pi, 0 ≤ ρ p) (hD : 0 ≤ D)
    (hQ : IsPathIn G Q) (hw : walkWeight G Q ≤ ENNReal.ofReal D)
    (p : V) (hp : p ∈ Pi) (a : ℕ) (ha : a < Q.length) :
    (Q[a] ∈ inBall G p (ρ p) →
        ∀ (a' : ℕ) (h' : a' ≤ a), Q[a']'(by omega) ∈ pivotBlock G p (ρ p) D) ∧
      (Q[a] ∈ outBall G p (ρ p) →
        ∀ (a' : ℕ) (h' : a ≤ a') (h'' : a' < Q.length), Q[a'] ∈ pivotBlock G p (ρ p) D) := by sorry

end SemiStreamReach.Main
