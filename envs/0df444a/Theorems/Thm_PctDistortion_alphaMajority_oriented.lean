-- Prove2me | Theorems.Thm_PctDistortion_alphaMajority_oriented
-- name    : PctDistortion.alphaMajority_oriented
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:42:30.16023+00:00
-- url     : https://prove2.me/theorems/3d5eb47a-2827-4c56-ad4b-e11ad629700f
-- title:
--   §2.3, p.10 — α-majority digraphs are oriented for $\alpha\ge 1/2$
-- statement:
--   For every $\alpha\ge1/2$ and every election $\mathcal E$, the α-majority digraph $G^\alpha_{\mathcal E}$ is oriented: it has no self-loops, and for no pair $c,c'$ are both $(c,c')$ and $(c',c)$ arcs.
--
--   This is used to apply Proposition 3 to α-majority digraphs and in the case $s=2$ of Theorem B.
--
--   Differences from the source:
--   - encoding: finite elections with n voters and m candidates → finite nonempty voter and candidate types; reason: the percentile cost and the lotteries presuppose n, m ≥ 1; with n = 0 the cost is undefined and with m = 0 there is no lottery
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), §2.3, p.10 (sentence after Definition 3)

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_PctDistortion_alphaMajority
import Definitions.Def_PctDistortion_inDeg

set_option autoImplicit false

namespace PctDistortion

/-- **α-majority digraphs are oriented**. Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), §2.3, p.10 (after Definition 3): "Note that each
α-majority digraph G^α_E for α ≥ 1/2 is oriented." -/
theorem alphaMajority_oriented (α : ℝ) (hα : 1 / 2 ≤ α) {V C : Type} [Fintype V] [Nonempty V]
    [Fintype C] [Nonempty C] (E : Election V C) : IsOriented (alphaMajority α E) := by sorry

end PctDistortion
