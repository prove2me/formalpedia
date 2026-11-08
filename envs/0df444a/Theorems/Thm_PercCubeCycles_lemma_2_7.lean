-- Prove2me | Theorems.Thm_PercCubeCycles_lemma_2_7
-- name    : PercCubeCycles.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:34:55.260588+00:00
-- url     : https://prove2.me/theorems/70050db3-ed9e-41e0-bd3f-5734a08a28aa
-- title:
--   Lemma 2.7 — every vertex of $Q^d$ is within distance two of the giant of $Q^d_{c/d}$
-- statement:
--   Let $c>1$ be constant and $p=c/d$. Whp every vertex $v\in V(Q^d)$ is within distance two in $Q^d$ from a vertex of the giant component $L_1$ of $Q^d_p$.
--
--   This density of the giant lets terminal sets be projected into it.
--
--   Differences from the source:
--   - reading: the giant component $L_1$ → every vertex set of a largest component; reason: the page assumes a unique giant; the statement for every largest component covers ties and is not the weaker reading
--   - encoding: distance two in $Q^d$ → Hamming distance at most $2$; reason: distance in $Q^d$ is the Hamming distance
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), Lemma 2.7 (part of [5, Lemma 7.7]), p.9

import Mathlib
import Definitions.Def_PercCubeCycles_GraphNotation
import Definitions.Def_PercCubeCycles_Trees
import Definitions.Def_PercCubeCycles_Percolation

set_option autoImplicit false

open RandomGames.BRD

namespace PercCubeCycles

/-- Lemma 2.7, p.9 (part of [5, Lemma 7.7]), Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…). Let `c > 1` be constant and `p = c/d`. Whp every
vertex `v ∈ V(Q^d)` is within distance two in `Q^d` from a vertex of the giant component `L₁` of `Q^d_p`.

**Formalization Note.** Distance in `Q^d` is Hamming distance. -/
theorem lemma_2_7 (c : ℝ) (hc : 1 < c) :
    Whp (fun d => c / d) fun d ω => ∀ L₁, IsLargestComponent (openGraph ω) L₁ →
      ∀ v : Profile d, ∃ u ∈ L₁, hammingDist v u ≤ 2 := by sorry

end PercCubeCycles
