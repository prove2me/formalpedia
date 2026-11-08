-- Prove2me | Theorems.Thm_PercCubeCycles_lemma_2_2
-- name    : PercCubeCycles.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:33:35.736198+00:00
-- url     : https://prove2.me/theorems/b95b5b07-2601-46c9-898d-37a7a011d9fc
-- title:
--   Lemma 2.2 — Harper's edge-isoperimetric inequality $e(S,S^c)\ge|S|(d-\log_2|S|)$
-- statement:
--   For every integer $d\ge1$ and every set $S\subseteq V(Q^d)$,
--   $$e(S,V(Q^d)\setminus S)\ge|S|\,(d-\log_2|S|).$$
--   This is Harper's inequality, stated on the full hypercube; it bounds the edges spanned by a small vertex set.
--
--   Differences from the source:
--   - encoding: $\log_2|S|$ at $S=\emptyset$ → `Real.logb 2 0 = 0`, so both sides are $0$; reason: the printed term is undefined there, and the inequality is trivially true
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), Lemma 2.2, p.6

import Mathlib
import Definitions.Def_PercCubeCycles_GraphNotation
import Definitions.Def_PercCubeCycles_Percolation

set_option autoImplicit false

open RandomGames.BRD

namespace PercCubeCycles

/-- Lemma 2.2, p.6 (Harper's edge-isoperimetric inequality), Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…). For every `d ≥ 1` and every
`S ⊆ V(Q^d)`, `e(S, V(Q^d) ∖ S) ≥ |S| (d − log₂ |S|)`.

**Formalization Note.** At `S = ∅` both sides are `0` (`Real.logb 2 0 = 0`). -/
theorem lemma_2_2 (d : ℕ) (hd : 1 ≤ d) (S : Finset (Profile d)) :
    (S.card : ℝ) * ((d : ℝ) - Real.logb 2 S.card) ≤ (eBetween (cube d) S Sᶜ : ℝ) := by sorry

end PercCubeCycles
