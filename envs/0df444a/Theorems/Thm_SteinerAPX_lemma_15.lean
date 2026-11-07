-- Prove2me | Theorems.Thm_SteinerAPX_lemma_15
-- name    : SteinerAPX.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:14.745705+00:00
-- url     : https://prove2.me/theorems/b813ff9d-99c0-4f66-aef1-51df558b76db
-- title:
--   Lemma 15 — the orthogonal routing is separated and has total length $L=O(m)$
-- statement:
--   There is a constant $C_1>0$ such that for every 3DM-3 instance $H=(U,E)$ with $m=|U|+|E|$, for every assignment of the labels of each square to its corners $\pm b_1,\pm b_2$ (and of each fallback to $\pm b_1$), the orthogonal routing of $H$ in $\mathbb R^{m+|U|+3}$ is a well-formed cable layout (its cables are pairwise disjoint trees of line segments through their ports), its cables are separated, and its total cable length satisfies
--   $$
--   L\le C_1\,m .
--   $$
--
--   With Theorem 7, this gives a constant-gap reduction from 3DM-3 to Euclidean Steiner Tree in linear dimension.
--
--   Differences from the source:
--   - reading: the cables of the orthogonal routing are separated → the routing is a well-formed cable layout (disjoint tree cables through their ports) and is separated; reason: Definition 6 applies to cable instances of §4.1, whose cables are disjoint trees; the proof shows the tree property ("so the cable is a tree") and the disjointness
--   - reading: the orthogonal routing (which corner of a square carries which label is not specified) → orthogonalRoutingWith H dir for every assignment dir sending the labels of each square bijectively onto {±b₁, ±b₂} and those of each fallback onto {±b₁} (IsOrthAssignment), C₁ chosen before H and dir; reason: the paper leaves the assignment open (§4.1: the ports "are the four points zs ± b1 and zs ± b2"), so the lemma is claimed for every choice; the stronger reading is taken
--   - encoding: a 3DM-3 instance H with three parts of size r → an Inst3DM, whose parts have size r ≥ 1; reason: excludes only the empty instance (no elements, no triples, no gadgets), which the paper never considers (it assumes 4r ≤ m, §2)
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), Lemma 15, p.20 (PDF p.22); proof pp.20–21

import Mathlib
import Definitions.Def_SteinerAPX_Separated
import Definitions.Def_SteinerAPX_orthogonalRouting

namespace SteinerAPX

open Inst3DM CableLayout

/-- **Lemma 15 (the orthogonal routing is separated and short).** S. Bartlmae, *Inapproximability
of Euclidean Steiner Tree*, STOC 2027 submission (manuscript sha256 6f78a9ea…), Lemma 15, p.20
(PDF p.22): "The cables of the orthogonal routing are separated and have total length L = O(m)."

There is a constant `C₁ > 0` such that for every 3DM-3 instance `H` and every assignment of the
port labels to the corners `±b₁, ±b₂` (at fallbacks `±b₁`), the orthogonal routing of `H` is a
well-formed cable layout (its cables are trees of segments through their ports, pairwise
disjoint), it is separated, and its total cable length is at most `C₁ · m` with `m = |U| + |E|`.

**Formalization Note** Well-formedness (cables disjoint trees of segments) is part of the claim: the
proof of (S2) on p.21 shows "so the cable is a tree", and §4.1 requires disjoint cables. The paper
leaves the label-to-corner assignment open, so the statement holds for every assignment
(`IsOrthAssignment`); `C₁` is chosen before the instance and the assignment. -/
theorem lemma_15 :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ H : Inst3DM, H.IsThreeDM3 →
      ∀ dir : Gadget H → Label H → EuclideanSpace ℝ (OrthIndex H), IsOrthAssignment H dir →
      (orthogonalRoutingWith H dir).WellFormed ∧ Separated (orthogonalRoutingWith H dir) ∧
      (orthogonalRoutingWith H dir).totalLen ≤ C₁ * (H.size : ℝ) := by sorry

end SteinerAPX
