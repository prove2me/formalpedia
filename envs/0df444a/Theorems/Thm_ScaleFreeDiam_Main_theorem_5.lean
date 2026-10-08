-- Prove2me | Theorems.Thm_ScaleFreeDiam_Main_theorem_5
-- name    : ScaleFreeDiam.Main.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:11:12.506424+00:00
-- url     : https://prove2.me/theorems/618de184-adef-43f2-9b9a-f229b30ded5b
-- title:
--   Theorem 5, p. 13 — for m ≥ 1, a.e. G_mⁿ has diam > log n/log(3Cm² log n), C the constant of Lemma 4
-- statement:
--   Let $C>0$ be a constant for which the bound of Lemma 4 holds, and let $m\ge1$ be fixed. Then for almost every $G_m^n\in\mathcal G_m^n$,
--   $$
--   \operatorname{diam}(G_m^n)>\frac{\log n}{\log(3Cm^2\log n)} ,
--   $$
--   a disconnected graph having infinite diameter.
--
--   This is the lower half of Theorem 1, in a sharper form and for every $m\ge1$.
--
--   **Formalization Note** "Where $C$ is the constant in Lemma 4" is rendered by assuming `Lemma4Bound C`: the conclusion holds for every constant for which Lemma 4 holds. The hypothesis $C>0$ is implied by `Lemma4Bound C` and is stated for readability. "$\operatorname{diam}>L$" is the negation of `AllWithin G L`, so a disconnected graph satisfies it (for $m=1$, $G_1^n$ is disconnected with high probability).
-- source:
--   Bollobás and Riordan, The diameter of a scale-free random graph, Combinatorica 24 (2004), p. 13, Theorem 5

import Mathlib
import Definitions.Def_ScaleFreeDiam_Main_Process

namespace ScaleFreeDiam.Main

open Filter Topology MeasureTheory ProbabilityTheory
open scoped Classical

theorem theorem_5 (C : ℝ) (hC : 0 < C) (hC4 : Lemma4Bound C) (m : ℕ) (hm : 1 ≤ m) :
    AlmostEvery m (fun n G =>
      ¬ AllWithin G (Real.log n / Real.log (3 * C * (m : ℝ) ^ 2 * Real.log n))) := by sorry

end ScaleFreeDiam.Main
