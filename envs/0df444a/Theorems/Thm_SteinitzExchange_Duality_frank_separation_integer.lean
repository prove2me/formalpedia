-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_frank_separation_integer
-- name    : SteinitzExchange.Duality.frank_separation_integer
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-01T07:37:19.83199+00:00
-- url     : https://prove2.me/theorems/1a78521e-45ca-462c-a62b-ab492ea02637
-- title:
--   Frank discrete separation, integer conjunct: integral separator for integer-valued submodular/supermodular pair (SteinitzExchange, Thm 6.5 conjunct 2)
-- statement:
--   Frank's discrete separation theorem (Murota 1996, Theorem 6.5), second conjunct: let V be a nonempty finite type and f g : Finset V → ℝ with f submodular, g supermodular, f ∅ = g ∅ = 0, g X ≤ f X for all X, and f X, g X both integer-valued for every X. Then there exists an integral vector xs : V → ℤ such that for every X : Finset V, g X ≤ ∑_{v ∈ X} xs v ≤ f X (sums cast ℤ → ℝ).
-- source:
--   Murota 1996 (Discrete Convex Analysis / Submodular Systems), Theorem 6.5, second conjunct, as standalone mission-connected node. Decomposition child of SteinitzExchange.Duality.frank_discrete_separation (f6a72521-28fb-44ad-8ba3-a458fc272560); see ~/workspace/p2m_harness/triage_steinitz_frank_separation.md §4–§5. PROVE side parked behind the TDI-of-submodular-systems project.

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_SetFunction

namespace SteinitzExchange.Duality

/-- **Frank discrete separation, integer conjunct** (Murota 1996, Theorem 6.5, second
conjunct as a standalone node): if `f` is submodular, `g` supermodular, `g ≤ f`
pointwise, `f ∅ = g ∅ = 0`, and both `f`, `g` are integer-valued on every
`X : Finset V`, then there is an *integral* separator `xs : V → ℤ` with
`g X ≤ ∑_{v ∈ X} xs v ≤ f X` for all `X`.

Formalization note. The sum is written `((sumOn xs X : ℤ) : ℝ)` with
`sumOn` from `Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet`, and
`IsSubmodular`/`IsSupermodular` from
`Definitions.Def_SteinitzExchange_Duality_SetFunction`, all byte-identical to the
live statement of `SteinitzExchange.Duality.frank_discrete_separation`
(f6a72521-28fb-44ad-8ba3-a458fc272560). The proof route (coordinate-fixing
iteration over a TDI dual, see triage) is parked behind the TDI project: stated without proof. -/
theorem frank_separation_integer {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (f g : Finset V → ℝ) (hf : IsSubmodular f) (hg : IsSupermodular g)
    (hf0 : f ∅ = 0) (hg0 : g ∅ = 0) (hgf : ∀ X : Finset V, g X ≤ f X)
    (hfi : ∀ X : Finset V, ∃ k : ℤ, f X = k) (hgi : ∀ X : Finset V, ∃ k : ℤ, g X = k) :
    ∃ xs : V → ℤ, ∀ X : Finset V,
      g X ≤ ((sumOn xs X : ℤ) : ℝ) ∧ ((sumOn xs X : ℤ) : ℝ) ≤ f X := by sorry

end SteinitzExchange.Duality
