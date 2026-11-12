-- Prove2me | Theorems.Thm_QSampVerif_lemma_3_15
-- name    : QSampVerif.lemma_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:31:39.709358+00:00
-- url     : https://prove2.me/theorems/828bf9f2-b679-4b66-9ce0-754f707a1938
-- title:
--   Lemma 3.15 — Margulis–Gabber–Galil edge expansion $|\partial A|\ge\frac{8-5\sqrt2}{2}|A|$
-- statement:
--   For every integer $r_G\ge1$, the Margulis–Gabber–Galil multigraph $G_{r_G}$ on $\mathbb Z_{r_G}^2$ (Definition 3.14) satisfies
--
--   $$|\partial A|\ge a_G|A|,\qquad a_G=\frac{8-5\sqrt2}{2},\qquad(40)$$
--
--   for every $A\subseteq\mathbb Z_{r_G}^2$ with $|A|\le r_G^2/2$, where $\partial A$ is the multiset of edges with exactly one endpoint in $A$.
--
--   This explicit expansion constant enters the RSP consistency tests through Lemma 3.16.
--
--   Differences from the source:
--   - encoding: the neighbour maps (39) with "Each map and its inverse specify opposite endpoints of the same edges"; r_G ≥ 1 → one edge s(v, f(v)) per vertex v and per forward map f; NeZero r; reason: each − map is the inverse of a + map, so this is the same multigraph (degree 8, loops counted twice)
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Lemma 3.15, (40), p.21 (PDF 22); Definition 3.14, (39)

import Definitions.Def_QSampVerif_mggGraph

set_option autoImplicit false

namespace QSampVerif

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7),
Lemma 3.15 (Margulis–Gabber–Galil edge expansion), (40), p.21 (PDF 22).

For every `r_G ≥ 1`, the graph `G_{r_G}` satisfies `|∂A| ≥ a_G |A|` for every `A ⊆ Z²_{r_G}` with
`|A| ≤ r_G²/2`, where `a_G = (8 − 5√2)/2`. -/
theorem lemma_3_15 (r : ℕ) [NeZero r] (A : Finset (ZMod r × ZMod r))
    (hA : (A.card : ℝ) ≤ (r : ℝ) ^ 2 / 2) :
    (8 - 5 * Real.sqrt 2) / 2 * (A.card : ℝ) ≤ ((mggGraph r).boundary A : ℝ) := by sorry

end QSampVerif
