-- Prove2me | Theorems.Thm_SFLOracleLowerBound_Hardness_concave_cardinality
-- name    : SFLOracleLowerBound.Hardness.concave_cardinality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T02:25:59.671619+00:00
-- url     : https://prove2.me/theorems/1016dd69-70ba-4806-97b8-86370ef370b2
-- title:
--   Lemma 3 — Concave cardinality functions
-- statement:
--   Let $E$ be finite, $W\subseteq E$, and $g:\mathbb R\to\mathbb R$ concave. Then
--   $$f(A)=g(|A\cap W|)$$
--   is submodular. If $g$ is also nondecreasing, $f$ is monotone.
--
--   This supplies the cardinality-composition fact used to analyze the split penalty. Neither normalization nor nonnegativity is assumed.
--
--   Differences from the source:
--   - encoding: finite ground sets and their subsets → finite types and Finset subsets; reason: bijections preserve every subset, cardinality and set operation
-- source:
--   Adam N. Elmachtoub, Bento Natura, Meike Neuwohner, Settling the Approximability of Submodular Facility Location, STOC 2027 submission #1249 (October 2026), Lemma 3, p.6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1249.pdf

import Mathlib
import Definitions.Def_SFLOracleLowerBound_Hardness_SetFunctions

set_option autoImplicit false

noncomputable section

namespace SFLOracleLowerBound.Hardness

open Classical Finset MeasureTheory
open scoped ENNReal

/-- Lemma 3, p.6. -/

theorem concave_cardinality {E : Type} [Fintype E] [DecidableEq E]
    (W : Finset E) (g : ℝ → ℝ) (hg : ConcaveOn ℝ Set.univ g) :
    NonmonotoneSubmod.Shared.Submodular (fun A : Finset E => g (A ∩ W).card) ∧
    (Monotone g → SetMonotone (fun A : Finset E => g (A ∩ W).card)) := by sorry

end SFLOracleLowerBound.Hardness
