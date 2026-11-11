-- Prove2me | Theorems.Thm_WaitFreeTasks_Characterization_proper_refinement
-- name    : WaitFreeTasks.Characterization.proper_refinement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:31:17.89058+00:00
-- url     : https://prove2.me/theorems/d3f83e06-2d94-4925-8282-9841b24d1960
-- title:
--   Lemma 12 — Proper Sperner refinement with image-carrier colors
-- statement:
--   Let $T=(I,O,\Delta)$ be a chromatic task for $n\ge2$ processes, with the finite complexes and chromatic, monotone, pure carrier of Section 2. Fix a carried PL finite-to-one map $f:|I|\to|O|$ and a geometric subdivision $D=\operatorname{div}(I)$ on whose simplices $f$ is affine and whose simplex images lie in output simplices, as in Section 4.1.
--
--   List all output simplices as $\Sigma_1,\ldots,\Sigma_m$ in nondecreasing dimension. A run means the actual push-down and descending shatter loops of Section 4.2, starting with $D$ and the minimum image-carrier coloring $\operatorname{col}$ of Definition 2. Write $K_t$ and $\operatorname{col}_t$ for its state after phase $t$, and $D'=K_m$, $\operatorname{col}'=\operatorname{col}_m$ for its output. No correctness invariant is assumed in the definition of a run.
--
--   For every nondecreasing-dimension order of all output simplices, a completed run exists. Its output is a geometric subdivision $D'$ of $D$ with coloring $\operatorname{col}'$ satisfying
--
--   $$\operatorname{col}'|_{V(D)}=\operatorname{col},\qquad\operatorname{col}'\text{ is proper and Sperner relative to }I,$$
--   $$\operatorname{col}'(v)\in\operatorname{id}_O(\operatorname{carr}_O(f(v)))\quad(v\in V(D')).$$
--
--   Proper means injective on every face. All old vertices keep their colors, and the final clause refers to the fixed original map $f$. The statement includes the existence of the procedure's completed run; it does not assume termination as input.
--
--   Differences from the source:
--   - encoding: maps between finite complex realizations → ambient real coordinate functions restricted to the realizations, with faces stored as finite sets; reason: every real barycentric point is included; values off the realizations are irrelevant and extend arbitrarily
--   - encoding: identifiers in [n] = {1,...,n} → identifiers in Fin n = {0,...,n-1}; reason: subtracting one is an order preserving bijection; all n >= 2 remain quantified
--   - encoding: states after the procedure handles each output simplex → a finite run relation with phase boundaries indexed by naturals; reason: only atomic stellar operations and loop exit tests are assumed; no successful-refinement invariant is an input
--   - generalization: existence of a proper Sperner refinement as produced in Section 4.2 → existence of a completed procedure run for every legal handling order, together with all source conclusions; reason: the finite-loop construction is valid for any dimension-respecting order and forgetting its run yields the printed statement
-- source:
--   Hagit Attiya, Ami Paz, STOC 2027 submission #828 (October 2026), p. 16 (PDF p. 18), Lemma 12

import Definitions.Def_WaitFreeTasks_Characterization_Refinement

set_option autoImplicit false

open Classical

namespace WaitFreeTasks.Characterization

/-- **Lemma 12** (Attiya–Paz, STOC 2027 submission #828 (October 2026), printed p. 16, PDF p. 18), in the strengthened form its proof gives.
Setting of §4: `T` is a chromatic task for `n ≥ 2` processes, `f : |I| → |O|` is PL,
finite-to-one and carried by `Δ`, and `D = div(I)` is a subdivision of `I` with the property of
Lemma 2 (`f` linear on each simplex of `D`, mapping it into a simplex of `O`).
For every handling order `Σ_1, …, Σ_m` of the simplices of `O` (non-decreasing dimension) the
refinement procedure has a completed run, and its output is a subdivision `div'(I)` of `div(I)`
with a colouring `col' : V(div'(I)) → [n]` that agrees with `col` on `V(div(I))`, is proper and
Sperner w.r.t. `I`, and satisfies `col'(v) ∈ id_O(carr_O(f(|v|)))` for every vertex `v`. -/
theorem proper_refinement {n : ℕ} {VI VO : Type} (hn : 2 ≤ n) (T : Task n VI VO)
    (f : (VI → ℝ) → (VO → ℝ)) (hPL : IsPL T.I.real f) (hfin : FiniteToOne T.I.real T.O.real f)
    (hcar : IsCarried T f) (D : GCx (VI → ℝ)) (hD : IsSubdivOf D T.I) (hDf : IsAdapted T f D) :
    ∀ ord : List (Finset VO), IsHandlingOrder T ord →
      ∃ st : ℕ → RState n VI, IsRun (by omega) T f D ord st ∧
        ∃ K' : GCx (VI → ℝ), K'.faces = (st ord.length).1 ∧ Refines K' D ∧
          (∀ v ∈ verts D.faces, (st ord.length).2 v = initColor (by omega) T f v) ∧
          IsProper K'.faces (st ord.length).2 ∧ IsSperner T K'.faces (st ord.length).2 ∧
          ∀ v ∈ verts K'.faces, (st ord.length).2 v ∈ (carrOf T.O.faces {f v}).image T.idO := by sorry

end WaitFreeTasks.Characterization
