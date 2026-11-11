-- Prove2me | Theorems.Thm_WaitFreeTasks_Characterization_original_colors
-- name    : WaitFreeTasks.Characterization.original_colors
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:30:51.091256+00:00
-- url     : https://prove2.me/theorems/4530eb72-dcca-4112-9fb3-4042f773128d
-- title:
--   Proposition 3 — Initial coloring agrees on original vertices
-- statement:
--   Let $T=(I,O,\Delta)$ be a chromatic task for $n\ge2$ processes, with the finite complexes and chromatic, monotone, pure carrier of Section 2. Fix a carried PL finite-to-one map $f:|I|\to|O|$ and a geometric subdivision $D=\operatorname{div}(I)$ on whose simplices $f$ is affine and whose simplex images lie in output simplices, as in Section 4.1.
--
--   For every original input vertex $v$, its standard basis point is still a vertex of $D$, and the coloring of Definition 2 agrees with its process identifier:
--
--   $$\{e_v\}\in D,\qquad \operatorname{col}(e_v)=\operatorname{id}_I(v)\quad(v\in V(I)).$$
--
--   Here $e_v$ is the realization of $v$, and $\operatorname{col}(x)$ is the minimum color in $\operatorname{carr}_O(f(x))$. The equality concerns the restriction to original vertices. It connects the new coloring with the original task identifiers.
--
--   Differences from the source:
--   - encoding: maps between finite complex realizations → ambient real coordinate functions restricted to the realizations, with faces stored as finite sets; reason: every real barycentric point is included; values off the realizations are irrelevant and extend arbitrarily
--   - encoding: identifiers in [n] = {1,...,n} → identifiers in Fin n = {0,...,n-1}; reason: subtracting one is an order preserving bijection; all n >= 2 remain quantified
--   - encoding: the coloring restricted to original vertices → explicit singleton membership in the subdivision together with color agreement; reason: this states the vertex inclusion inherent in the source restriction without identifying two different vertex domains
-- source:
--   Hagit Attiya, Ami Paz, STOC 2027 submission #828 (October 2026), p. 10 (PDF p. 12), Proposition 3

import Definitions.Def_WaitFreeTasks_Characterization_Refinement

set_option autoImplicit false

open Classical

namespace WaitFreeTasks.Characterization

/-- **Proposition 3** (Attiya–Paz, STOC 2027 submission #828 (October 2026), printed p. 10, PDF p. 12). Setting of §4: `T` is a chromatic task for `n ≥ 2` processes, `f : |I| → |O|` is PL,
finite-to-one and carried by `Δ`, and `D = div(I)` is a subdivision of `I` with the property of
Lemma 2 (`f` linear on each simplex of `D`, mapping it into a simplex of `O`).
The colouring `col` of Definition 2 coincides on the original vertices `V(I) ⊆ V(div(I))` with
the original colouring `id_I`. -/
theorem original_colors {n : ℕ} {VI VO : Type} (hn : 2 ≤ n) (T : Task n VI VO)
    (f : (VI → ℝ) → (VO → ℝ)) (hPL : IsPL T.I.real f) (hfin : FiniteToOne T.I.real T.O.real f)
    (hcar : IsCarried T f) (D : GCx (VI → ℝ)) (hD : IsSubdivOf D T.I) (hDf : IsAdapted T f D) :
    ∀ v ∈ verts T.I.faces, {vpt v} ∈ D.faces ∧ initColor (by omega) T f (vpt v) = T.idI v := by sorry

end WaitFreeTasks.Characterization
