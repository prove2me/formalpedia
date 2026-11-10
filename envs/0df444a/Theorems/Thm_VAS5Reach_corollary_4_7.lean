-- Prove2me | Theorems.Thm_VAS5Reach_corollary_4_7
-- name    : VAS5Reach.corollary_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:29:44.224195+00:00
-- url     : https://prove2.me/theorems/be2d3daa-05be-4205-8cb6-f64720f9af5b
-- title:
--   Corollary 4.7 — thresholds survive reversal and adjoining sign-definite transitions zero on $I$
-- statement:
--   Let $V$ be a $(d+2)$-VAS with transition set $T$, $I$ a set of two coordinates, $B \in \mathbb N$, and let $C$ be a transformation-area threshold for $[\![V]\!]_{I,B}$. Then $C$ is also a transformation-area threshold for $[\![V^{\mathrm{REV}}]\!]_{I,B}$, where $V^{\mathrm{REV}} = -V$ has transition set $-T$, and for $[\![V']\!]_{I,B}$ whenever $V'$ is obtained from $V$ by adjoining finitely many transitions in $\{(0,0)\} \times (\mathbb N^d \cup (-\mathbb N^d))$, i.e. vectors that vanish on $I$ and are either nonnegative or nonpositive on the remaining coordinates.
--
--   Differences from the source:
--   - generalization: [[V]]_B with I the first two coordinates (assumed w.l.o.g., p.16) → [[V]]_{I,B} for every set I of two coordinates; reason: renaming coordinates maps any pair to the first two, so the paper's case I = {1, 2} is an instance
--   - encoding: adjoining transitions in {(0, 0)} × (ℕ^d ∪ (−ℕ^d)) → T ∪ A for any finite set A of vectors that vanish on I and are each ≥ 0 or ≤ 0 off I; reason: a VAS has finitely many transitions
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Corollary 4.7, p.19 (PDF p.21); −V for a VAS, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_VAS5Reach_IsTAThreshold

namespace VAS5Reach

/-- **Corollary 4.7.** Let `V` be a `(d + 2)`-VAS and `B ∈ ℕ`. Let `C` be any transformation-area
threshold for `[[V]]_B`. The same `C` is a transformation-area threshold for `[[V^REV]]_B` and for
`[[V′]]_B` whenever `V′` is obtained from `V` by adjoining transitions in
`{(0, 0)} × (ℕ^d ∪ (−ℕ^d))`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Corollary 4.7, printed p. 19 (PDF p. 21); for a VAS, `V^REV = −V` (printed p. 14,
PDF p. 16: "For a VAS, we also write −V for the reversed system").

**Formalization Note** The encoded pair `I` is any two coordinates (the paper fixes the first two
w.l.o.g.); an adjoined vector is zero on `I` and, on the other coordinates, either everywhere
`≥ 0` or everywhere `≤ 0` (each vector separately); any finite set `A` of them is adjoined. -/
theorem corollary_4_7 {ι : Type} [Fintype ι] [DecidableEq ι] (T : Finset (ι → ℤ)) (I : Finset ι)
    (B C : ℕ) (hI : I.card = 2) (hC : IsTAThreshold T I B C) :
    IsTAThreshold (T.image fun a => -a) I B C ∧
    ∀ A : Finset (ι → ℤ),
      (∀ a ∈ A, (∀ i ∈ I, a i = 0) ∧ ((∀ i ∉ I, 0 ≤ a i) ∨ (∀ i ∉ I, a i ≤ 0))) →
      IsTAThreshold (T ∪ A) I B C := by sorry

end VAS5Reach
