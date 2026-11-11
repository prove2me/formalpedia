-- Prove2me | Theorems.Thm_SAInterp_Res2_lemma_2_6
-- name    : SAInterp.Res2.lemma_2_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:37:42.296752+00:00
-- url     : https://prove2.me/theorems/ca1cbc88-e698-4852-989c-b92820a8aa93
-- title:
--   Lemma 2.6 — a non-witnessing degree-d design forces NS_R(F) > d; a non-witnessing degree-d pseudoexpectation forces SA(F) > d
-- statement:
--   Let $F$ be a CNF over a finite set of variables and let $d\in\mathbb N$.
--   - If $F$ admits a degree-$d$ $F$-nonwitnessing design (Definition 2.4), then every $\mathbb R$-Nullstellensatz refutation of $F$ has degree $>d$, that is, $\mathrm{NS}_{\mathbb R}(F)>d$.
--   - If $F$ admits a degree-$d$ $F$-nonwitnessing pseudoexpectation (Definition 2.5), then every Sherali-Adams refutation of $F$ in the dual-variable encoding has degree $>d$, that is, $\mathrm{SA}(F)>d$.
--   $$\exists\,\tilde E\ \text{degree-}d\text{ nonwitnessing pseudoexpectation}\ \Longrightarrow\ \mathrm{SA}(F)>d.$$
--   This is the lower-bound principle of the paper: Theorem 8.1 applies it to the booleanized CPLS pseudoexpectation.
--
--   Differences from the source:
--   - reading: NS_R(F) > d and SA(F) > d (minimum degree of a refutation) → every refutation has degree > d; reason: equivalent, and avoids Lean's `sInf ∅ = 0` when F has no refutation.
--   - encoding: a design D : P_d(n) → ℝ → a function on all of ℝ[x, x̄] constrained only on polynomials of degree ≤ d, with p ∈ P_{d−2}, P_{d−1} written deg p + 2 ≤ d, deg p + 1 ≤ d; reason: Lean convention, same designs (the zero polynomial is handled by linearity).
-- source:
--   Acheampong, Davis, Robere, Polynomial Interpolation for Sherali-Adams Lower Bounds, STOC 2027 submission (manuscript sha256 8de0a787…), p. 18 (PDF p. 20), Lemma 2.6

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_SAInterp_Res2_SherAdams

open MultiplierAssoc206.Resolution

namespace SAInterp.Res2

/-- Lemma 2.6 (p. 18): a degree-`d` non-witnessing design for `F` forces every
`ℝ`-Nullstellensatz refutation of `F` to have degree `> d` (`NS_ℝ(F) > d`); a degree-`d`
non-witnessing pseudoexpectation forces every Sherali-Adams refutation of `F` to have degree
`> d` (`SA(F) > d`). -/
theorem lemma_2_6 {α : Type} [Fintype α] (F : CNF α) (d : ℕ) :
    ((∃ D : DualPoly α → ℝ, IsDesign d D ∧ IsNonwitnessing F d D) →
      ∀ π : NSRefutation F, d < π.degree) ∧
    ((∃ D : DualPoly α → ℝ, IsPseudoexpectation d D ∧ IsNonwitnessing F d D) →
      ∀ π : SARefutation F, d < π.degree) := by sorry

end SAInterp.Res2
