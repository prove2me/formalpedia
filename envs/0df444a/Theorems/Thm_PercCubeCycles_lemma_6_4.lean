-- Prove2me | Theorems.Thm_PercCubeCycles_lemma_6_4
-- name    : PercCubeCycles.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:34:37.594436+00:00
-- url     : https://prove2.me/theorems/15214816-535d-48c5-9c9f-4143202d9e02
-- title:
--   Lemma 6.4 — connected sets of medium size span at most $(1+\varepsilon^{12})|U|$ edges
-- statement:
--   Let $m,M$ be as in Theorem 6. Under the standing assumptions of §6, whp every connected set $U$ in $Q^d_p$ with $m/d^4\le|U|\le Md^6$ spans at most $(1+\varepsilon^{12})|U|$ edges in $Q^d_p$.
--
--   This limits surplus edges, and so the leaves of the second type of special tree.
--
--   Differences from the source:
--   - encoding: $\varepsilon$ sufficiently small → $\exists\varepsilon_0>0\ \forall\varepsilon\in(0,\varepsilon_0)$; reason: the standard meaning of the phrase
--   - encoding: connected set → the induced graph is connected, so the empty set is excluded; reason: the size bound excludes it anyway
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), Lemma 6.4 with the event $\mathcal E$, p.21

import Mathlib
import Definitions.Def_PercCubeCycles_GraphNotation
import Definitions.Def_PercCubeCycles_Trees
import Definitions.Def_PercCubeCycles_Percolation

set_option autoImplicit false

open RandomGames.BRD

namespace PercCubeCycles

/-- Lemma 6.4, p.21, Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…). Under the standing assumptions of §6, whp every connected set `U` in `Q^d_p`
with `m/d⁴ ≤ |U| ≤ Md⁶` spans at most `(1 + ε¹²)|U|` edges in `Q^d_p`. -/
theorem lemma_6_4 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Whp (supercritical ε) fun d ω => ∀ U : Finset (Profile d), IsConnectedSet (openGraph ω) U →
        mLow ε d / (d : ℝ) ^ 4 ≤ (U.card : ℝ) → (U.card : ℝ) ≤ mHigh ε d * (d : ℝ) ^ 6 →
        (edgesIn (openGraph ω) U : ℝ) ≤ (1 + ε ^ 12) * U.card := by sorry

end PercCubeCycles
