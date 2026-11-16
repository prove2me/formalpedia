-- Prove2me | Theorems.Thm_TopicalIrreducibility_Relations_Supplement_theorem_3_5
-- name    : TopicalIrreducibility.Relations.Supplement.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:21:12.118043+00:00
-- url     : https://prove2.me/theorems/ed7094dd-276d-4847-9a4c-2a6ecec25b16
-- title:
--   Theorem 3.5 — partial irreducibility implies imperturbability, with the converse for subadditive maps
-- statement:
--   Fix a finite dimension $n$ and let $f:\mathbb R^n_{\ge0}\to\mathbb R^n_{\ge0}$ be m-topical. Then:
--
--   1. if $f$ is partially irreducible, then $f$ is imperturbable;
--   2. if $f$ is subadditive, i.e. $f(x+y)\le f(x)+f(y)$ for all $x,y\in\mathbb R^n_{\ge0}$, and imperturbable, then $f$ is partially irreducible.
--
--   Together with Theorem 2.4 this places partial irreducibility and imperturbability in the hierarchy of irreducibility notions for topical maps: the two are equivalent for subadditive maps, while in general partial irreducibility is the stronger condition.
--
--   Differences from the source:
--   - encoding: parts P_J and invariance f(P_J) ⊆ P_J for nonempty proper J → Set.MapsTo f (part J) (part J) with the base IsNontrivialProper; reason: same condition
--   - encoding: lim_{t→∞} f(1+te_J)_i < ∞ → a finite bound on the ray t ≥ 0 for each i ∉ J; reason: the ray is monotone for an order-preserving f, so the limit is finite iff the ray is bounded
-- source:
--   Brian Lins, Irreducibility for Topical Maps, STOC 2027 submission #201 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/201.pdf, Theorem 3.5, pp. 7–8 (PDF pp. 7–8); Definitions 3.1, 3.3, p. 6

import Mathlib
import Definitions.Def_TopicalIrreducibility_Relations_MTopical
import Definitions.Def_TopicalIrreducibility_Relations_Supplement_Conditions

open scoped NNReal

namespace TopicalIrreducibility.Relations.Supplement

open TopicalIrreducibility.Relations

/-- Theorem 3.5 (pp. 7–8). Let `f` be m-topical on `ℝⁿ_{≥0}`.
(1) If `f` is partially irreducible, then it is imperturbable.
(2) If `f` is subadditive and imperturbable, then it is partially irreducible. -/
theorem theorem_3_5 {n : ℕ} (f : StdCone n → StdCone n) (hf : IsMTopical f) :
    (PartiallyIrreducible f → Imperturbable f) ∧
      (IsSubadditive f → Imperturbable f → PartiallyIrreducible f) := by sorry

end TopicalIrreducibility.Relations.Supplement
