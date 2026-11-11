-- Prove2me | Theorems.Thm_WaitFreeTasks_Characterization_carrier_support
-- name    : WaitFreeTasks.Characterization.carrier_support
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:31:01.930087+00:00
-- url     : https://prove2.me/theorems/c26fa931-5433-4402-a4e2-533002929637
-- title:
--   Claim 15 — Image carriers are supported at an interior point
-- statement:
--   Let $T=(I,O,\Delta)$ be a chromatic task for $n\ge2$ processes, with the finite complexes and chromatic, monotone, pure carrier of Section 2. Fix a carried PL finite-to-one map $f:|I|\to|O|$ and a geometric subdivision $D=\operatorname{div}(I)$ on whose simplices $f$ is affine and whose simplex images lie in output simplices, as in Section 4.1.
--
--   List all output simplices as $\Sigma_1,\ldots,\Sigma_m$ in nondecreasing dimension. A run means the actual push-down and descending shatter loops of Section 4.2, starting with $D$ and the minimum image-carrier coloring $\operatorname{col}$ of Definition 2. Write $K_t$ and $\operatorname{col}_t$ for its state after phase $t$, and $D'=K_m$, $\operatorname{col}'=\operatorname{col}_m$ for its output. No correctness invariant is assumed in the definition of a run.
--
--   Let $\sigma'\in D'$, and let $x$ be a relative interior point of its geometric simplex. For every vertex $v\in\sigma'$,
--
--   $$\operatorname{carr}_O(f(v))\subseteq\operatorname{carr}_O(f(x)).$$
--
--   The relative interior condition is essential; an arbitrary boundary point does not have this property. The map is unchanged during refinement and remains affine on these simplices. This is the local support assertion in the proof of Lemma 14.
--
--   Differences from the source:
--   - encoding: maps between finite complex realizations → ambient real coordinate functions restricted to the realizations, with faces stored as finite sets; reason: every real barycentric point is included; values off the realizations are irrelevant and extend arbitrarily
--   - encoding: identifiers in [n] = {1,...,n} → identifiers in Fin n = {0,...,n-1}; reason: subtracting one is an order preserving bijection; all n >= 2 remain quantified
--   - encoding: states after the procedure handles each output simplex → a finite run relation with phase boundaries indexed by naturals; reason: only atomic stellar operations and loop exit tests are assumed; no successful-refinement invariant is an input
-- source:
--   Hagit Attiya, Ami Paz, STOC 2027 submission #828 (October 2026), p. 17 (PDF p. 19), Claim 15

import Definitions.Def_WaitFreeTasks_Characterization_Refinement

set_option autoImplicit false

open Classical

namespace WaitFreeTasks.Characterization

/-- **Claim 15** (Attiya–Paz, STOC 2027 submission #828 (October 2026), printed p. 17, PDF p. 19; stated inside the proof of Lemma 14).
Setting of §4: `T` is a chromatic task for `n ≥ 2` processes, `f : |I| → |O|` is PL,
finite-to-one and carried by `Δ`, and `D = div(I)` is a subdivision of `I` with the property of
Lemma 2 (`f` linear on each simplex of `D`, mapping it into a simplex of `O`).
Let `Σ_1, …, Σ_m` (`ord`) be the simplices of `O` in the non-decreasing order of dimension
in which they are handled, and let `st` be a completed run of the refinement procedure of §4.2
from `(div(I), col)`, so that `K_t = (st t).1` (with colouring `(st t).2`) is the subdivision
after handling `Σ_t`. For every simplex `σ'` of `div'(I)`, every point `x` in the interior of `|σ'|` and every
vertex `v ∈ σ'`, `carr_O(f(|v|)) ⊆ carr_O(f(x))`. -/
theorem carrier_support {n : ℕ} {VI VO : Type} (hn : 2 ≤ n) (T : Task n VI VO)
    (f : (VI → ℝ) → (VO → ℝ)) (hPL : IsPL T.I.real f) (hfin : FiniteToOne T.I.real T.O.real f)
    (hcar : IsCarried T f) (D : GCx (VI → ℝ)) (hD : IsSubdivOf D T.I) (hDf : IsAdapted T f D)
    (ord : List (Finset VO)) (hord : IsHandlingOrder T ord) (st : ℕ → RState n VI)
    (hrun : IsRun (by omega) T f D ord st) :
    ∀ σ' ∈ (st ord.length).1, ∀ x ∈ openSimplex σ', ∀ v ∈ σ',
      carrOf T.O.faces {f v} ⊆ carrOf T.O.faces {f x} := by sorry

end WaitFreeTasks.Characterization
