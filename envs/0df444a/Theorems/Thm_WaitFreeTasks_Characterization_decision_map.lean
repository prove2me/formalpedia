-- Prove2me | Theorems.Thm_WaitFreeTasks_Characterization_decision_map
-- name    : WaitFreeTasks.Characterization.decision_map
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:31:08.667654+00:00
-- url     : https://prove2.me/theorems/5762993d-79c9-49fe-83f1-606f66406557
-- title:
--   Lemma 13 — Decision map is well defined, simplicial and chromatic
-- statement:
--   Let $T=(I,O,\Delta)$ be a chromatic task for $n\ge2$ processes, with the finite complexes and chromatic, monotone, pure carrier of Section 2. Fix a carried PL finite-to-one map $f:|I|\to|O|$ and a geometric subdivision $D=\operatorname{div}(I)$ on whose simplices $f$ is affine and whose simplex images lie in output simplices, as in Section 4.1.
--
--   List all output simplices as $\Sigma_1,\ldots,\Sigma_m$ in nondecreasing dimension. A run means the actual push-down and descending shatter loops of Section 4.2, starting with $D$ and the minimum image-carrier coloring $\operatorname{col}$ of Definition 2. Write $K_t$ and $\operatorname{col}_t$ for its state after phase $t$, and $D'=K_m$, $\operatorname{col}'=\operatorname{col}_m$ for its output. No correctness invariant is assumed in the definition of a run.
--
--   For each actual vertex $v$ of $D'$, there is a unique vertex $w$ of its output image carrier with color $\operatorname{col}'(v)$. This defines a vertex map $\phi:V(D')\to V(O)$ satisfying
--
--   $$\phi(v)\in\operatorname{carr}_O(f(v)),\qquad\operatorname{id}_O(\phi(v))=\operatorname{col}'(v),$$
--   $$\phi(\sigma)\in O\quad(\sigma\in D').$$
--
--   Existence of this map is part of the conclusion. Every map obeying Definition 5 has these properties; chromaticity makes its choices unique. The actual vertex domain permits the empty vertex map when both complexes are empty.
--
--   Differences from the source:
--   - encoding: maps between finite complex realizations → ambient real coordinate functions restricted to the realizations, with faces stored as finite sets; reason: every real barycentric point is included; values off the realizations are irrelevant and extend arbitrarily
--   - encoding: identifiers in [n] = {1,...,n} → identifiers in Fin n = {0,...,n-1}; reason: subtracting one is an order preserving bijection; all n >= 2 remain quantified
--   - encoding: states after the procedure handles each output simplex → a finite run relation with phase boundaries indexed by naturals; reason: only atomic stellar operations and loop exit tests are assumed; no successful-refinement invariant is an input
--   - encoding: the unique image-carrier vertex of the assigned color → a relation on maps from the actual vertex subtype; reason: Lemma 13 establishes existence and pointwise uniqueness; empty domains require no output default
-- source:
--   Hagit Attiya, Ami Paz, STOC 2027 submission #828 (October 2026), p. 16 (PDF p. 18), Lemma 13

import Definitions.Def_WaitFreeTasks_Characterization_Refinement

set_option autoImplicit false

open Classical

namespace WaitFreeTasks.Characterization

/-- **Lemma 13** (Attiya–Paz, STOC 2027 submission #828 (October 2026), printed p. 16, PDF p. 18). Setting of §4: `T` is a chromatic task for `n ≥ 2` processes, `f : |I| → |O|` is PL,
finite-to-one and carried by `Δ`, and `D = div(I)` is a subdivision of `I` with the property of
Lemma 2 (`f` linear on each simplex of `D`, mapping it into a simplex of `O`).
Let `Σ_1, …, Σ_m` (`ord`) be the simplices of `O` in the non-decreasing order of dimension
in which they are handled, and let `st` be a completed run of the refinement procedure of §4.2
from `(div(I), col)`, so that `K_t = (st t).1` (with colouring `(st t).2`) is the subdivision
after handling `Σ_t`. The map `φ : div'(I) → O` of Definition 5 is well defined (for every vertex `v` of
`div'(I)` there is exactly one vertex of `carr_O(f(|v|))` of colour `col'(v)`), simplicial and
colour-preserving. -/
theorem decision_map {n : ℕ} {VI VO : Type} (hn : 2 ≤ n) (T : Task n VI VO)
    (f : (VI → ℝ) → (VO → ℝ)) (hPL : IsPL T.I.real f) (hfin : FiniteToOne T.I.real T.O.real f)
    (hcar : IsCarried T f) (D : GCx (VI → ℝ)) (hD : IsSubdivOf D T.I) (hDf : IsAdapted T f D)
    (ord : List (Finset VO)) (hord : IsHandlingOrder T ord) (st : ℕ → RState n VI)
    (hrun : IsRun (by omega) T f D ord st) :
    (∀ v ∈ verts (st ord.length).1,
      ∃! w : VO, w ∈ carrOf T.O.faces {f v} ∧ T.idO w = (st ord.length).2 v) ∧
    (∃ φ : VertexMap (st ord.length).1 VO,
      IsDecisionMap T f (st ord.length).1 (st ord.length).2 φ) ∧
    ∀ φ : VertexMap (st ord.length).1 VO,
      IsDecisionMap T f (st ord.length).1 (st ord.length).2 φ →
      (∀ σ ∈ (st ord.length).1, vertexImage (st ord.length).1 σ φ ∈ T.O.faces) ∧
      ∀ v, T.idO (φ v) = (st ord.length).2 v.val := by sorry

end WaitFreeTasks.Characterization
