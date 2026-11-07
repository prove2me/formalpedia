-- Prove2me | Theorems.Thm_PctDistortion_proposition_3
-- name    : PctDistortion.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:41:47.276443+00:00
-- url     : https://prove2.me/theorems/01a56318-baaf-4bd4-93cf-345addda41d6
-- title:
--   Proposition 3 — the ABC value of an oriented digraph is at least $1/|V|$
-- statement:
--   Let $G=(V,E)$ be an oriented digraph (no self-loops and no 2-cycles) on a finite nonempty node set. Then
--   $$\nu(\mathcal G^{ABC}_G)\ge\frac{1}{|V|}.$$
--   Since every α-majority digraph with $\alpha\ge1/2$ is oriented, this gives Corollary 3 and settles the case $s=2$ of Theorem B.
--
--   Differences from the source:
--   - encoding: "|V|" for a digraph G = (V, E) → a finite nonempty node type; reason: 1/|V| and "a vertex" presuppose |V| ≥ 1
--   - encoding: ν = Alice's payoff under any equilibrium → Alice's maximin value (abcValue); reason: equal by the minimax theorem; the maximin value exists for every finite game
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Proposition 3, p.17 (proof App. G.2, p.45)

import Mathlib
import Definitions.Def_PctDistortion_inDeg
import Definitions.Def_PctDistortion_abcValue

set_option autoImplicit false

namespace PctDistortion

/-- **Proposition 3** (positive value on oriented digraphs). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Proposition 3, p.17 (proof
App. G.2, p.45): if `G = (V, E)` is oriented (no loops, no 2-cycles), then `ν(G^ABC_G) ≥ 1/|V|`.

**Formalization Note.** `V` is a finite nonempty node type; `ν` is `abcValue` (Alice's maximin
value, equal to her payoff at every equilibrium). -/
theorem proposition_3 {W : Type} [Fintype W] [Nonempty W] (G : Digraph W) (hG : IsOriented G) :
    1 / (Fintype.card W : ℝ) ≤ abcValue G := by sorry

end PctDistortion
