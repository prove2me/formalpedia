-- Prove2me | Theorems.Thm_PlanarDFVSKernel_lemma_3_6
-- name    : PlanarDFVSKernel.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:35:33.946453+00:00
-- url     : https://prove2.me/theorems/62874398-234a-4b67-89fa-388db35d493a
-- title:
--   Lemma 3.6 — Reduction Rule 4 is safe
-- statement:
--   **Lemma 3.6 (Reduction Rule 4 is safe).** Let $D$ be a plane digraph in which Reduction Rules 1 to 3 are no longer applicable (as in Lemma 3.5), and let $v$ be a vertex that appears on the boundaries of more than $k(k+2)$ directed faces. Then
--   1. every directed feedback vertex set of size at most $k$ contains $v$;
--   2. $(D,k)$ is a YES-instance if and only if $k\ge1$ and $(D-v,k-1)$ is a YES-instance.
--
--   A directed face is a face whose boundary is a nonempty closed walk following the arc directions. Reduction Rule 4 deletes $v$ and sets $k\leftarrow k-1$.
--
--   Differences from the source:
--   - generalization: a planar input after Reduction Rules 1 to 3 → a drawing of any digraph with the four reduced properties of Rules 1–2 and with Rule 3 inapplicable; no Rule 1 (iii)/(iv) budget outcomes; reason: the proof uses only these properties (via Lemma 3.5)
--   - generalization: Reduction Rule 4 is safe (equivalence) → the equivalence plus the forced-vertex statement (every solution of size ≤ k contains v); reason: the forced-vertex statement is proved in the source's proof; the conjunction implies the printed claim
--   - encoding: the reduced instance (D − v, k − 1) → 1 ≤ k ∧ FeasibleOn G (V ∖ {v}) (k − 1); reason: no renumbering; for k = 0 both sides are NO
--   - encoding: directed faces → the published circularFaces (dart orbits with all corners alternating); reason: the same faces: a face orbit has all corners alternating exactly when its boundary walk follows the arcs in one direction
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), Lemma 3.6 and Reduction Rule 4, p.11 (PDF 12)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs
import Definitions.Def_PlanarDFVSKernel_FeasibleOn
import Definitions.Def_PlanarDFVSKernel_ReducedRules12
import Definitions.Def_PlanarDFVSKernel_ccDel
import Definitions.Def_PlanarDFVSKernel_dirFacesAt

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp

/-- **Lemma 3.6 (Reduction Rule 4 is safe)** (Sheng, Xiao, *A Polynomial Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256 75cfca8f…), Lemma 3.6, p.11 (PDF 12)): "Reduction Rule 4.
If a vertex v appears on the boundaries of more than k(k + 2) directed faces, delete v and set
k ← k − 1. Lemma 3.6. Reduction Rule 4 is safe."

In a plane digraph where Reduction Rules 1 to 3 are no longer applicable, if `v` appears on the
boundaries of more than `k(k + 2)` directed faces, then every directed feedback vertex set of size
at most `k` contains `v`, and `(D, k)` is a YES-instance exactly when `k ≥ 1` and
`(D − v, k − 1)` is a YES-instance.

**Formalization Note** Directed faces are the published `circularFaces E`. The guard `1 ≤ k`
makes `k − 1` exact; for `k = 0` both sides are false. -/
theorem lemma_3_6 {n m : ℕ} {G : Graph n m} (E : Drawing G) (k : ℕ) (hred : ReducedRules12 G)
    (hR3 : ∀ x y : Fin n, x ≠ y → SameSCC G x y → ccDel G x y ≤ k)
    (v : Fin n) (hv : k * (k + 2) < dirFacesAt E v) :
    (∀ X : Finset (Fin n), IsDFVS G X → X.card ≤ k → v ∈ X) ∧
    (Feasible G k ↔ 1 ≤ k ∧ FeasibleOn G (Finset.univ \ {v}) (k - 1)) := by sorry

end PlanarDFVSKernel
