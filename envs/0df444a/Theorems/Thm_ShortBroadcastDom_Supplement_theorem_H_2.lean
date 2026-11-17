-- Prove2me | Theorems.Thm_ShortBroadcastDom_Supplement_theorem_H_2
-- name    : ShortBroadcastDom.Supplement.theorem_H_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:47:34.266221+00:00
-- url     : https://prove2.me/theorems/4e9b4a04-94e2-449f-b64f-8bba2222cf74
-- title:
--   Theorem H.2 — no constant-round LOCAL algorithm achieves $(4-\varepsilon)\tau_c$ for planar red-blue domination
-- statement:
--   Let $\varepsilon>0$ and $t\ge0$. No deterministic $t$-round LOCAL algorithm returns, on every feasible planar red-blue instance, a set of blue vertices that covers all red vertices and has size at most $(4-\varepsilon)\tau_c$. This holds even if the network is connected, has maximum degree four and has $\tau_c=\mathrm{OPT}_c$, if the vertices know $n$, and if the identifiers are exactly $1,\dots,n$.
--
--   Here a red-blue instance colours every vertex red or blue; a solution is a set of blue vertices such that every red vertex has a chosen blue neighbour, the instance is feasible when every red vertex has a blue neighbour, and $\tau_c$, $\mathrm{OPT}_c$ are the fractional and integral optima of this covering problem. With Corollary H.1(ii) this makes four the infimum of the achievable coefficients for planar red-blue domination, set cover and hitting set.
--
--   **Formalization Note** The witness carries unit costs; every vertex knows $n$ and its colour.
--
--   Differences from the source:
--   - reading: deterministic T-round LOCAL algorithm (after T rounds a vertex knows the labelled radius-(T+1) ball with identifiers, degrees, port numbers, and n) → a BroadcastAlg without message bound, local input n, identifiers a bijection onto {1,…,n}, output after T rounds; reason: full-information broadcast with distinct identifiers simulates the paper's convention in T+2 rounds with identifier-ordered ports, so the statement for every T implies the paper's
--   - reading: size at most (4−ε)τc, τc = OPTc → unit costs: |D| ≤ (4−ε)·τ_c and τ_c = OPT_c with all costs 1; reason: the bound compares a size with τ_c, and the instances of the proof have unit costs (τ_c = OPT_c = L²/4 per patch)
--   - encoding: red/blue colouring → col : V → Bool (true = red); reason: two colours
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), App. H, p.103 (PDF p.106), Theorem H.2; setting p.102 (PDF p.105)

import Mathlib
import Definitions.Def_ShortBroadcastDom_BroadcastAlg
import Definitions.Def_ShortBroadcastDom_Supplement_tauRel
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar

namespace ShortBroadcastDom.Supplement

open ShortBroadcastDom

/-- **Theorem H.2 (coefficient four is optimal for planar red-blue domination).** Amiri, Siebertz,
Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix f4dc98d2), App. H,
p.103 (PDF 106): "Let ε > 0 and t ≥ 0. No deterministic t-round LOCAL algorithm returns, on every
feasible planar red-blue instance, a set of blue vertices that covers all red vertices and has size
at most (4 − ε)τc. This holds even if the network is connected, has maximum degree four, and has
τc = OPTc, if the vertices know n, and if the identifiers are exactly 1, . . . , n." Setting (p.102):
vertices are red or blue, a solution is a set of blue vertices such that every red vertex has a
chosen blue neighbour; this is the covering instance with demands the red vertices and `C(r)` the
blue neighbours of `r`, with unit costs ("size").

**Formalization Note** The colouring is `col : V → Bool` (`true` = red, `false` = blue); a
vertex's local input is `(n, its colour)`. A deterministic `t`-round LOCAL algorithm is a
`BroadcastAlg` with no message bound run for `t` rounds, with identifiers a bijection onto
`{1, …, n}`; as for Theorem F.12, the labelled-ball convention of p.87 is simulated in `t + 2`
broadcast rounds with identifier-ordered ports, so the statement for every `t` implies the paper's.
The witness is connected, planar, of maximum degree at most four, feasible (every red vertex has a
blue neighbour) and has `τ_c = OPT_c` (unit costs); on it the output is not a set of blue vertices
covering every red vertex of size at most `(4 − ε)τ_c`. -/
theorem theorem_H_2 (ε : ℝ) (hε : 0 < ε) (t : ℕ) (alg : BroadcastAlg (ℕ × Bool) Bool) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj)
      (id : V → ℕ) (col : V → Bool),
      G.Connected ∧ RobertsonSeymour1986.GM5.IsPlanar G ∧ (∀ v, G.degree v ≤ 4) ∧
      (∀ r, col r = true → ∃ u, G.Adj r u ∧ col u = false) ∧
      tauRel (Finset.univ.filter fun r => col r = true)
          (fun r => (G.neighborFinset r).filter fun u => col u = false) (fun _ => 1) =
        optRel (Finset.univ.filter fun r => col r = true)
          (fun r => (G.neighborFinset r).filter fun u => col u = false) (fun _ => 1) ∧
      Function.Injective id ∧ (∀ v, 1 ≤ id v ∧ id v ≤ Fintype.card V) ∧
      ¬ ((∀ v ∈ alg.outSet G id (fun v => (Fintype.card V, col v)) t, col v = false) ∧
        (∀ r, col r = true → ∃ v ∈ alg.outSet G id (fun v => (Fintype.card V, col v)) t,
          G.Adj r v) ∧
        ((alg.outSet G id (fun v => (Fintype.card V, col v)) t).card : ℝ) ≤
          (4 - ε) * tauRel (Finset.univ.filter fun r => col r = true)
            (fun r => (G.neighborFinset r).filter fun u => col u = false) (fun _ => 1)) := by sorry

end ShortBroadcastDom.Supplement
