-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_frank_separation_real
-- name    : SteinitzExchange.Duality.frank_separation_real
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-01T14:38:10.364917+00:00
-- url     : https://prove2.me/theorems/ce70432e-0b7b-42f5-bbd8-20ffa37343e8
-- title:
--   Frank discrete separation, real case: real separator for submodular/supermodular pair (SteinitzExchange, Thm 6.5 conjunct 1)
-- statement:
--   Frank's discrete separation theorem (Murota 1996, Theorem 6.5), real case: let V be a nonempty finite type and f g : Finset V → ℝ with f submodular (f (X ∪ Y) + f (X ∩ Y) ≤ f X + f Y), g supermodular (g X + g Y ≤ g (X ∪ Y) + g (X ∩ Y)), f ∅ = g ∅ = 0, and g X ≤ f X for all X. Then there exists a real separator xs : V → ℝ with g X ≤ ∑ v ∈ X, xs v ≤ f X for all X. This is the first conjunct of Theorem 6.5; the integer-valued strengthening is the standalone node SteinitzExchange.Duality.frank_separation_integer (1a78521e), and the affine Farkas certificate used in the proof route is SteinitzExchange.Duality.farkas_affine_form1 (84e2d072).
-- source:
--   Murota 1996 (Discrete Convex Analysis / Submodular Systems), Theorem 6.5, first conjunct (real case), as standalone mission-connected node. Decomposition child of SteinitzExchange.Duality.frank_discrete_separation (f6a72521-28fb-44ad-8ba3-a458fc272560); sibling of frank_separation_integer (Thm 6.5 conjunct 2).

import Mathlib

namespace SteinitzExchange.Duality

/-- **Frank discrete separation, real case** (Murota 1996, Theorem 6.5, first
conjunct as a standalone node): if `f` is submodular, `g` supermodular, `g ≤ f`
pointwise, and `f ∅ = g ∅ = 0`, then there is a *real* separator `xs : V → ℝ`
with `g X ≤ ∑ v ∈ X, xs v ≤ f X` for all `X`.

Formalization note. Submodularity and supermodularity are spelled out in
Mathlib-native form so the node is self-contained: `IsSubmodular f` means
`∀ X Y, f (X ∪ Y) + f (X ∩ Y) ≤ f X + f Y` and `IsSupermodular g` means
`∀ X Y, g X + g Y ≤ g (X ∪ Y) + g (X ∩ Y)` (the predicates used in
`Definitions.Def_SteinitzExchange_Duality_SetFunction` on the integer conjunct
`frank_separation_integer`, 1a78521e-45ca-462c-a62b-ab492ea02637). The proof
route reduces to the affine Farkas certificate
`SteinitzExchange.Duality.farkas_affine_form1`
(84e2d072-a88f-42fb-9cc9-cfa15b2bb6ba), applied to the constraint family
`{x(X) ≤ f X, -x(X) ≤ -g X}` over `X : Finset V`. Stated without proof. -/
theorem frank_separation_real {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (f g : Finset V → ℝ)
    (hf : ∀ X Y : Finset V, f (X ∪ Y) + f (X ∩ Y) ≤ f X + f Y)
    (hg : ∀ X Y : Finset V, g X + g Y ≤ g (X ∪ Y) + g (X ∩ Y))
    (hf0 : f ∅ = 0) (hg0 : g ∅ = 0) (hgf : ∀ X : Finset V, g X ≤ f X) :
    ∃ xs : V → ℝ, ∀ X : Finset V,
      g X ≤ Finset.sum X (fun v => xs v) ∧ Finset.sum X (fun v => xs v) ≤ f X := by
  sorry

end SteinitzExchange.Duality
