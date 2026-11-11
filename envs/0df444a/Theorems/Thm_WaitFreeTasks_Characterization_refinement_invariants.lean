-- Prove2me | Theorems.Thm_WaitFreeTasks_Characterization_refinement_invariants
-- name    : WaitFreeTasks.Characterization.refinement_invariants
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:31:19.138278+00:00
-- url     : https://prove2.me/theorems/9b812c4a-2be0-45e4-9e41-b5a277a40eae
-- title:
--   Lemma 10 — Refinement invariants at phase boundaries
-- statement:
--   Let $T=(I,O,\Delta)$ be a chromatic task for $n\ge2$ processes, with the finite complexes and chromatic, monotone, pure carrier of Section 2. Fix a carried PL finite-to-one map $f:|I|\to|O|$ and a geometric subdivision $D=\operatorname{div}(I)$ on whose simplices $f$ is affine and whose simplex images lie in output simplices, as in Section 4.1.
--
--   List all output simplices as $\Sigma_1,\ldots,\Sigma_m$ in nondecreasing dimension. A run means the actual push-down and descending shatter loops of Section 4.2, starting with $D$ and the minimum image-carrier coloring $\operatorname{col}$ of Definition 2. Write $K_t$ and $\operatorname{col}_t$ for its state after phase $t$, and $D'=K_m$, $\operatorname{col}'=\operatorname{col}_m$ for its output. No correctness invariant is assumed in the definition of a run.
--
--   For any such completed run and every $1\le s\le t\le m$, all three conclusions hold:
--
--   $$\operatorname{pre}_f^{K_t}(\Sigma_s)=\operatorname{pre}_f^{K_s}(\Sigma_s),\qquad \operatorname{col}_t=\operatorname{col}_s\text{ on its vertices};$$
--   $$v\in V(\operatorname{pre}_f^{K_t}(\Sigma_t)),\quad v\text{ created in phase }s\quad\Longrightarrow\quad\operatorname{carr}_O(f(v))=\Sigma_s;$$
--   $$\operatorname{pre}_f^{K_t}(\Sigma_t)\text{ is properly colored}.$$
--
--   Creation in phase $s$ means membership in $V(K_s)\setminus V(K_{s-1})$. The states are produced by the procedure rather than being arbitrary complexes satisfying these invariants. These conclusions control preservation across phases.
--
--   Differences from the source:
--   - encoding: maps between finite complex realizations → ambient real coordinate functions restricted to the realizations, with faces stored as finite sets; reason: every real barycentric point is included; values off the realizations are irrelevant and extend arbitrarily
--   - encoding: identifiers in [n] = {1,...,n} → identifiers in Fin n = {0,...,n-1}; reason: subtracting one is an order preserving bijection; all n >= 2 remain quantified
--   - encoding: states after the procedure handles each output simplex → a finite run relation with phase boundaries indexed by naturals; reason: only atomic stellar operations and loop exit tests are assumed; no successful-refinement invariant is an input
-- source:
--   Hagit Attiya, Ami Paz, STOC 2027 submission #828 (October 2026), p. 14 (PDF p. 16), Lemma 10

import Definitions.Def_WaitFreeTasks_Characterization_Refinement

set_option autoImplicit false

open Classical

namespace WaitFreeTasks.Characterization

/-- **Lemma 10** (Attiya–Paz, STOC 2027 submission #828 (October 2026), printed p. 14, PDF p. 16). Setting of §4: `T` is a chromatic task for `n ≥ 2` processes, `f : |I| → |O|` is PL,
finite-to-one and carried by `Δ`, and `D = div(I)` is a subdivision of `I` with the property of
Lemma 2 (`f` linear on each simplex of `D`, mapping it into a simplex of `O`).
Let `Σ_1, …, Σ_m` (`ord`) be the simplices of `O` in the non-decreasing order of dimension
in which they are handled, and let `st` be a completed run of the refinement procedure of §4.2
from `(div(I), col)`, so that `K_t = (st t).1` (with colouring `(st t).2`) is the subdivision
after handling `Σ_t`. For all `1 ≤ s ≤ t ≤ m`:
1. `pre^{K_t}_f(Σ_s) = pre^{K_s}_f(Σ_s)`, and the colourings agree on its vertices;
2. every vertex `v` of `pre^{K_t}_f(Σ_t)` created while handling `Σ_s` (a vertex of `K_s` but
   not of `K_{s-1}`) satisfies `carr_O(f(|v|)) = Σ_s`;
3. `pre^{K_t}_f(Σ_t)` is properly coloured. -/
theorem refinement_invariants {n : ℕ} {VI VO : Type} (hn : 2 ≤ n) (T : Task n VI VO)
    (f : (VI → ℝ) → (VO → ℝ)) (hPL : IsPL T.I.real f) (hfin : FiniteToOne T.I.real T.O.real f)
    (hcar : IsCarried T f) (D : GCx (VI → ℝ)) (hD : IsSubdivOf D T.I) (hDf : IsAdapted T f D)
    (ord : List (Finset VO)) (hord : IsHandlingOrder T ord) (st : ℕ → RState n VI)
    (hrun : IsRun (by omega) T f D ord st) :
    ∀ s t : ℕ, 1 ≤ s → s ≤ t → t ≤ ord.length →
      ∀ Ss St : Finset VO, ord[s - 1]? = some Ss → ord[t - 1]? = some St →
        (pre (st t).1 f Ss = pre (st s).1 f Ss ∧
          ∀ v ∈ verts (pre (st s).1 f Ss), (st t).2 v = (st s).2 v) ∧
        (∀ v ∈ verts (pre (st t).1 f St), v ∈ verts (st s).1 → v ∉ verts (st (s - 1)).1 →
          carrOf T.O.faces {f v} = Ss) ∧
        IsProper (pre (st t).1 f St) (st t).2 := by sorry

end WaitFreeTasks.Characterization
