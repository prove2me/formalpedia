-- Prove2me | Theorems.Thm_SteinerAPX_lemma_11
-- name    : SteinerAPX.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:55.819598+00:00
-- url     : https://prove2.me/theorems/6e13abe6-fe07-4f3d-bf63-9c66a880f774
-- title:
--   Lemma 11 — the samples on a middle segment can be joined inside its tube at added length $\le\rho w+2\rho^2+4\rho\sqrt w$
-- statement:
--   Let a well-formed, separated cable layout of a 3DM-3 instance in $\mathbb R^D$ be given, $0<\rho\le1/100$, and let $T$ be a network spanning $P_\rho$. Let $(a,b)$ be a middle segment of a cable segment $e$, let $Z$ be its tube, and let $w=\mathcal H^1(|T|\cap Z)$ be the length of $T$ inside $Z$. Then there is a set $A$ of edges between consecutive sampled terminals of $e$, all lying on $[a,b]$, with
--   $$
--   \operatorname{len}(A)\le\rho w+2\rho^2+4\rho\sqrt w,
--   $$
--   such that all sampled terminals of $e$ on $[a,b]$ lie in one connected component of $(|T|\cap Z)\cup|A|$.
--
--   Summed over all tubes with Cauchy–Schwarz, this bounds the length needed to make a tree on $P_\rho$ follow every cable.
--
--   Differences from the source:
--   - generalization: T a tree of length O(L) spanning on Pρ → T any network with connected carrier containing Pρ; reason: the proof uses only that T is connected and contains Pρ; every tree spanning Pρ is such a network, so the statement specializes to the source's
--   - encoding: w the length of T inside Z → the one-dimensional Hausdorff measure of T ∩ Z; reason: this is the length of the set T ∩ Z; it is at most the summed length of the pieces of T's segments in Z
--   - encoding: connect all sampled terminals on that segment within Z by adding edges between consecutive terminals → a set A of consecutive-sample edges with both ends on [a, b] such that the samples on [a, b] lie in one connected component of (T ∩ Z) ∪ A; reason: the edges between samples on the middle segment lie in Z; one component is what "connect" means
--   - generalization: b₁, b₂ two orthogonal unit coordinate vectors of ℝᴰ → b₁, b₂ any orthonormal pair (CableLayout.WellFormed) in any EuclideanSpace ℝ ι; reason: a linear isometry of ℝᴰ maps any orthonormal pair onto two coordinate vectors and preserves every quantity in the statement, so the statement specializes to the source's coordinate vectors
--   - encoding: a 3DM-3 instance H with three parts of size r → an Inst3DM, whose parts have size r ≥ 1; reason: excludes only the empty instance (no elements, no triples, no gadgets), which the paper never considers (it assumes 4r ≤ m, §2)
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), Lemma 11, p.15 (PDF p.17), with the standing assumption "Fix a tree T of length O(L) spanning Pρ" (p.15)

import Mathlib
import Definitions.Def_SteinerAPX_Separated
import Definitions.Def_SteinerAPX_tube

namespace SteinerAPX

open Inst3DM CableLayout

/-- **Lemma 11 (joining the samples inside a tube).** S. Bartlmae, *Inapproximability of Euclidean
Steiner Tree*, STOC 2027 submission (manuscript sha256 6f78a9ea…), Lemma 11, p.15 (PDF p.17), in
the setting "Fix a tree T of length O(L) spanning Pρ" (p.15): "Let Z be the tube around a middle
segment and w the length of T inside Z. We can connect all sampled terminals on that segment within
Z by adding edges between consecutive terminals, with total added length at most
ρw + 2ρ2 + 4ρ√w."

For a well-formed, separated layout of a 3DM-3 instance in `ℝᴰ`, `0 < ρ ≤ 1/100`, a connected
network `T` containing `Pρ`, a cable segment `e` with a middle segment `(a, b)`, its tube `Z`, and
`w` the length of `T` inside `Z`: there is a set `A` of edges between consecutive samples of `e`,
all with both ends on `[a, b]`, of total length at most `ρw + 2ρ² + 4ρ√w`, such that any two samples
of `e` on `[a, b]` lie in one connected component of `(T ∩ Z) ∪ A`.

**Formalization Note** `T` is any network with connected carrier containing `Pρ`; a tree is one.
The length bound `len T = O(L)` of the setting is not used by this lemma and is dropped. `w` is the
one-dimensional Hausdorff measure of `T ∩ Z` (`lengthIn`), which is at most the summed length of
the parts of `T`'s segments inside `Z`. -/
theorem lemma_11 {ι : Type} [Fintype ι] (H : Inst3DM)
    (L : CableLayout H (EuclideanSpace ℝ ι)) (hH : H.IsThreeDM3) (hL : L.WellFormed)
    (hsep : Separated L) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 100)
    (T : Network (EuclideanSpace ℝ ι)) (hT : Spans (samples L ρ) T)
    (i : Label H) (e : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (he : e ∈ L.cable i)
    (a b : EuclideanSpace ℝ ι) (hab : IsMiddle ρ e.1 e.2 a b) :
    ∃ A : Network (EuclideanSpace ℝ ι),
      (∀ f ∈ A, f ∈ sampleEdges e.1 e.2 ρ ∧ f.1 ∈ segment ℝ a b ∧ f.2 ∈ segment ℝ a b) ∧
      len A ≤ ρ * lengthIn T (tube a b ρ) + 2 * ρ ^ 2 +
        4 * ρ * Real.sqrt (lengthIn T (tube a b ρ)) ∧
      ∀ x ∈ segSamples e.1 e.2 ρ ∩ segment ℝ a b, ∀ y ∈ segSamples e.1 e.2 ρ ∩ segment ℝ a b,
        y ∈ connectedComponentIn ((carrier T ∩ tube a b ρ) ∪ carrier A) x := by sorry

end SteinerAPX
