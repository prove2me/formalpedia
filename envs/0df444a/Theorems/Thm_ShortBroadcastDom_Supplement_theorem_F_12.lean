-- Prove2me | Theorems.Thm_ShortBroadcastDom_Supplement_theorem_F_12
-- name    : ShortBroadcastDom.Supplement.theorem_F_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:45:41.742053+00:00
-- url     : https://prove2.me/theorems/6e4986d7-c8d6-4c08-9adb-376d58bc4015
-- title:
--   Theorem F.12 — no constant-round LOCAL algorithm achieves $(6-\varepsilon)\gamma_{t,f}$ on planar or $(4-\varepsilon)\gamma_{t,f}$ on triangle-free planar graphs
-- statement:
--   Let $\varepsilon>0$ and $T\ge0$. No deterministic $T$-round LOCAL algorithm returns, on every connected planar graph $G$, a total dominating set of size at most $(6-\varepsilon)\gamma_{t,f}(G)$. No such algorithm achieves $(4-\varepsilon)\gamma_{t,f}(G)$ on every connected triangle-free planar graph. This holds even if the vertices know $n$ and the identifiers are exactly $1,\dots,n$.
--
--   Together with Theorem F.1 this shows that the coefficients $6$ (planar) and $4$ (triangle-free planar) for total domination are optimal.
--
--   **Formalization Note** For each claim: for every algorithm there is a witness, a connected planar (resp. connected planar triangle-free) graph without isolated vertices, with identifiers a bijection onto $\{1,\dots,n\}$ and $n$ given to every vertex, on which the output is not a total dominating set within the bound.
--
--   Differences from the source:
--   - reading: deterministic T-round LOCAL algorithm (after T rounds a vertex knows the labelled radius-(T+1) ball with identifiers, degrees, port numbers, and n) → a BroadcastAlg without message bound, local input n, identifiers a bijection onto {1,…,n}, output after T rounds; reason: full-information broadcast with distinct identifiers simulates the paper's convention in T+2 rounds with identifier-ordered ports, so the statement for every T implies the paper's
--   - reading: on every connected planar graph G → the witness is connected, planar and isolate-free; reason: the one-vertex graph has no total dominating set, which would make the claim trivial; γ_{t,f} is defined only on isolate-free graphs (p.86)
--   - encoding: triangle-free → G.CliqueFree 3; reason: Mathlib's notion of having no triangle
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), App. F.7, p.86 (PDF p.89), Theorem F.12; convention p.87 (PDF p.90)

import Mathlib
import Definitions.Def_ShortBroadcastDom_BroadcastAlg
import Definitions.Def_ShortBroadcastDom_Supplement_IsTotalDom
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar

namespace ShortBroadcastDom.Supplement

open ShortBroadcastDom

/-- **Theorem F.12 (LOCAL lower bounds for total domination on planar graphs).** Amiri, Siebertz,
Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix f4dc98d2), App. F.7,
p.86 (PDF 89): "Let ε > 0 and T ≥ 0. No deterministic T-round Local algorithm returns, on every
connected planar graph G, a total dominating set of size at most (6 − ε)γt,f(G). No such algorithm
achieves (4 − ε)γt,f(G) on every connected triangle-free planar graph. This holds even if the
vertices know n and the identifiers are exactly 1, . . . , n."

**Formalization Note** A deterministic `T`-round LOCAL algorithm is a `BroadcastAlg` with no
message bound whose local input is `n` (every vertex knows `n`), run for `T` rounds, with
identifiers a bijection onto `{1, …, n}`. With unbounded messages and distinct identifiers,
full-information broadcast learns the labelled ball: the paper's convention (p.87: after `T` rounds
a vertex knows the labelled radius-`(T + 1)` ball with identifiers, degrees, port numbers and `n`)
is simulated in `T + 2` broadcast rounds with identifier-ordered port numbers, so the statement for
every `T` implies the paper's. For each claim, every algorithm fails on some witness: a connected
planar graph (triangle-free in the second claim, `CliqueFree 3`) with no isolated vertex (the
one-vertex graph has no total dominating set, which would make the claim trivial), on which the
output is not a total dominating set of size at most the bound. -/
theorem theorem_F_12 (ε : ℝ) (hε : 0 < ε) (T : ℕ) (alg : BroadcastAlg ℕ Bool) :
    (∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj)
      (id : V → ℕ),
      G.Connected ∧ IsolateFree G ∧ RobertsonSeymour1986.GM5.IsPlanar G ∧
      Function.Injective id ∧ (∀ v, 1 ≤ id v ∧ id v ≤ Fintype.card V) ∧
      ¬ (IsTotalDom G (alg.outSet G id (fun _ => Fintype.card V) T) ∧
        ((alg.outSet G id (fun _ => Fintype.card V) T).card : ℝ) ≤ (6 - ε) * totFracDom G)) ∧
    (∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj)
      (id : V → ℕ),
      G.Connected ∧ IsolateFree G ∧ RobertsonSeymour1986.GM5.IsPlanar G ∧ G.CliqueFree 3 ∧
      Function.Injective id ∧ (∀ v, 1 ≤ id v ∧ id v ≤ Fintype.card V) ∧
      ¬ (IsTotalDom G (alg.outSet G id (fun _ => Fintype.card V) T) ∧
        ((alg.outSet G id (fun _ => Fintype.card V) T).card : ℝ) ≤ (4 - ε) * totFracDom G)) := by sorry

end ShortBroadcastDom.Supplement
