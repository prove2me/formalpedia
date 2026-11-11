-- Prove2me | Theorems.Thm_WaitFreeTasks_Characterization_initial_sperner
-- name    : WaitFreeTasks.Characterization.initial_sperner
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:31:05.941915+00:00
-- url     : https://prove2.me/theorems/3ab0ab02-9798-4e89-a52c-e1357665d333
-- title:
--   Lemma 4 — Initial coloring is Sperner
-- statement:
--   Let $T=(I,O,\Delta)$ be a chromatic task for $n\ge2$ processes, with the finite complexes and chromatic, monotone, pure carrier of Section 2. Fix a carried PL finite-to-one map $f:|I|\to|O|$ and a geometric subdivision $D=\operatorname{div}(I)$ on whose simplices $f$ is affine and whose simplex images lie in output simplices, as in Section 4.1.
--
--   The coloring of Definition 2 is Sperner relative to the original input complex:
--
--   $$\operatorname{col}(\sigma)\subseteq\operatorname{id}_I(\operatorname{carr}_I(\sigma))\quad(\sigma\in D).$$
--
--   For a fine simplex, its input carrier is the smallest original face containing its whole geometric simplex. The color set on the left is the set of colors of its vertices. This property limits new colors to processes present in that carrier.
--
--   Differences from the source:
--   - encoding: maps between finite complex realizations → ambient real coordinate functions restricted to the realizations, with faces stored as finite sets; reason: every real barycentric point is included; values off the realizations are irrelevant and extend arbitrarily
--   - encoding: identifiers in [n] = {1,...,n} → identifiers in Fin n = {0,...,n-1}; reason: subtracting one is an order preserving bijection; all n >= 2 remain quantified
-- source:
--   Hagit Attiya, Ami Paz, STOC 2027 submission #828 (October 2026), p. 10 (PDF p. 12), Lemma 4

import Definitions.Def_WaitFreeTasks_Characterization_Refinement

set_option autoImplicit false

open Classical

namespace WaitFreeTasks.Characterization

/-- **Lemma 4** (Attiya–Paz, STOC 2027 submission #828 (October 2026), printed p. 10, PDF p. 12). Setting of §4: `T` is a chromatic task for `n ≥ 2` processes, `f : |I| → |O|` is PL,
finite-to-one and carried by `Δ`, and `D = div(I)` is a subdivision of `I` with the property of
Lemma 2 (`f` linear on each simplex of `D`, mapping it into a simplex of `O`).
The colouring `col` of Definition 2 of `div(I)` is Sperner w.r.t. the colouring `id_I` of `I`. -/
theorem initial_sperner {n : ℕ} {VI VO : Type} (hn : 2 ≤ n) (T : Task n VI VO)
    (f : (VI → ℝ) → (VO → ℝ)) (hPL : IsPL T.I.real f) (hfin : FiniteToOne T.I.real T.O.real f)
    (hcar : IsCarried T f) (D : GCx (VI → ℝ)) (hD : IsSubdivOf D T.I) (hDf : IsAdapted T f D) :
    IsSperner T D.faces (initColor (by omega) T f) := by sorry

end WaitFreeTasks.Characterization
