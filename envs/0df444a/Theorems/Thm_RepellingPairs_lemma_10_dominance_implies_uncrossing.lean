-- Prove2me | Theorems.Thm_RepellingPairs_lemma_10_dominance_implies_uncrossing
-- name    : RepellingPairs.lemma_10_dominance_implies_uncrossing
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:02:04.127953+00:00
-- url     : https://prove2.me/theorems/fb72d95a-33fa-4202-ac2e-23936cf7fc09
-- title:
--   Lemma 10 (corrected: equal degrees, multisets, degenerate uncrossing)
-- statement:
--   Let $C,C'$ be configurations (multisets of chords) on $n$ points of a circle, with no loop in $C$ and equal degree at every point. If $C\succ C'$, then $C\to C'$: a finite sequence of moves leads from $C$ to $C'$, each one an uncrossing of two crossing chords or a degenerate move $(x,y),(x,w)\to(x,x),(y,w)$ with $x\notin\{y,w\}$.
--
--   Since each move does not increase the cost under a Kalmanson metric, this gives the cost comparison that finishes Theorem 1.
--
--   Differences from the source:
--   - correction: for any configurations C, C′, if C ≻ C′ then C → C′ → C has no loop and deg C = deg C′ at every point; reason: the printed statement is false: for n = 4, C = {(1,3), (2,4)} strictly dominates C′ = {(1,2)}, and a move preserves the number of chords. The proof itself uses Property 4 ("flows F, F′ are aligned", p.13)
--   - correction: C → C′ by uncrossing moves on chords with four distinct endpoints → the degenerate move (x,y), (x,w) → (x,x), (y,w) is also allowed; reason: needed once C′ has loops, which trivial paths of F′ create: for n = 3, C = {(1,2), (1,3)} and C′ = {(1,1), (2,3)} have equal degrees and C ≻ C′, yet C has no crossing pair. The move is the image of a printed uncrossing under the vertex splitting of p.13
--   - encoding: a configuration is a set of chords, n even → a multiset of chords; no parity condition; reason: two units of flow may share a pair; evenness belongs to the matching case
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), Lemma 10, p.11

import Mathlib
import Definitions.Def_RepellingPairs_Config

set_option autoImplicit false

namespace RepellingPairs

/-- **Lemma 10 (corrected: equal degrees, multisets, degenerate uncrossing).** For configurations with no loop in `C`,
equal degrees at every point and `C ≻ C′`, a finite sequence of uncrossing moves leads from `C` to `C′`.
Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version of October 23, 2026), Lemma 10, p.11.

**Formalization Note.** The printed statement has no degree condition and is false: on four points,
`C = {(1,3),(2,4)}` strictly dominates `C′ = {(1,2)}`, and a move preserves the number of chords. Its proof uses
Property 4. Loops in `C′`, created by the trivial paths of the normalization, need the degenerate move. -/
theorem lemma_10_dominance_implies_uncrossing {n : ℕ} (C C' : Config n)
    (hloop : ∀ a, s(a, a) ∉ C) (hdeg : ∀ t, Config.deg C t = Config.deg C' t)
    (h : Config.StrictlyDominates C C') : Config.Reaches C C' := by sorry

end RepellingPairs
