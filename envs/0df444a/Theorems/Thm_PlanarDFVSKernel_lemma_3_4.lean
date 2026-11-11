-- Prove2me | Theorems.Thm_PlanarDFVSKernel_lemma_3_4
-- name    : PlanarDFVSKernel.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:35:40.435107+00:00
-- url     : https://prove2.me/theorems/2b4abfc5-ad1c-4e7d-8d55-2c570d42c6c2
-- title:
--   Lemma 3.4 — Reduction Rule 3 is safe
-- statement:
--   **Lemma 3.4 (Reduction Rule 3 is safe).** Let $D$ be a digraph in which Reduction Rules 1 and 2 are no longer applicable: it has no loops and no repeated arcs with the same direction (opposite arcs allowed), every weakly connected component is strongly connected, and every vertex has at least two distinct incoming and two distinct outgoing neighbours. Let $x\ne y$ lie in one strongly connected component $D_0$, and suppose $D_0-\{x,y\}$ has more than $k$ weakly connected components. Then
--   1. every directed feedback vertex set of size at most $k$ contains both $x$ and $y$;
--   2. $(D,k)$ is a YES-instance if and only if $k\ge2$ and $(D-\{x,y\},k-2)$ is a YES-instance.
--
--   Reduction Rule 3 deletes $x,y$ and sets $k\leftarrow k-2$; the lemma says this preserves the answer.
--
--   Differences from the source:
--   - generalization: the setting of PDFVS (planar input) after Reduction Rules 1 and 2 → any digraph with the four reduced properties (no loops, no repeated arcs with the same direction, every arc inside one strongly connected component, at least two distinct in- and out-neighbours); no planarity and no Rule 1 (iii)/(iv) budget outcomes; reason: the proof uses only these properties (Lemma 3.3); every reduced planar instance satisfies them
--   - generalization: Reduction Rule 3 is safe (equivalence) → the equivalence plus the forced-vertex statement (every solution of size ≤ k contains x and y); reason: the forced-vertex statement is proved in the source's proof; the conjunction implies the printed claim
--   - encoding: the reduced instance (D − {x, y}, k − 2) → 2 ≤ k ∧ FeasibleOn G (V ∖ {x, y}) (k − 2); reason: the kept vertex set avoids renumbering; the guard makes the natural subtraction exact, and for k ≤ 1 the source's negative budget is a NO-instance, as is the Lean right-hand side
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), Lemma 3.4 and Reduction Rule 3, p.10 (PDF 11)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs
import Definitions.Def_PlanarDFVSKernel_FeasibleOn
import Definitions.Def_PlanarDFVSKernel_ReducedRules12
import Definitions.Def_PlanarDFVSKernel_ccDel

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp

/-- **Lemma 3.4 (Reduction Rule 3 is safe)** (Sheng, Xiao, *A Polynomial Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256 75cfca8f…), Lemma 3.4, p.10 (PDF 11)):
"Reduction Rule 3. If there are distinct vertices x, y in a strongly connected component D such that
D − {x, y} has more than k weakly connected components, delete x, y and set k ← k − 2. Lemma 3.4.
Reduction Rule 3 is safe."

Assume Reduction Rules 1 and 2 are no longer applicable. Let `x ≠ y` lie in one strongly connected
component `D` with `cc(D − {x, y}) > k`. Then every directed feedback vertex set of size at most
`k` contains `x` and `y`, and `(D, k)` is a YES-instance exactly when `k ≥ 2` and
`(D − {x, y}, k − 2)` is a YES-instance.

**Formalization Note** Safety (p.8 (PDF 9): "A reduction rule is safe if it produces an equivalent
instance") is the equivalence; the "every solution contains x and y" part of the proof is stated
too. The guard `2 ≤ k` makes the natural subtraction `k − 2` exact; for `k ≤ 1` both sides
are false. No planarity is assumed. -/
theorem lemma_3_4 {n m : ℕ} (G : Graph n m) (k : ℕ) (hred : ReducedRules12 G)
    (x y : Fin n) (hxy : x ≠ y) (hscc : SameSCC G x y) (hcc : k < ccDel G x y) :
    (∀ X : Finset (Fin n), IsDFVS G X → X.card ≤ k → x ∈ X ∧ y ∈ X) ∧
    (Feasible G k ↔ 2 ≤ k ∧ FeasibleOn G (Finset.univ \ {x, y}) (k - 2)) := by sorry

end PlanarDFVSKernel
