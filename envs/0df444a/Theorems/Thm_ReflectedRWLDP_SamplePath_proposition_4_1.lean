-- Prove2me | Theorems.Thm_ReflectedRWLDP_SamplePath_proposition_4_1
-- name    : ReflectedRWLDP.SamplePath.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:13.123999+00:00
-- url     : https://prove2.me/theorems/dbf61118-74a0-4bfc-90a0-81f413a13d73
-- title:
--   Proposition 4.1 — $y\mapsto\mathcal B^*_y$ is non-increasing and Lipschitz on $[0,\bar y]$, and $\mathcal B^*_y\in(0,\infty)$ on $[0,\bar y)$
-- statement:
--   Under the standing assumptions (i.i.d. increments with mean $\mu<0$, Assumptions 2.1–2.3, $p>0$), let $\mathcal B^*_y$ be the value of $(\mathcal B_y)$ and $\bar y=(|\mu|(p+1))^\alpha$. Then:
--
--   1. $y\mapsto\mathcal B^*_y$ is non-increasing on $[0,\bar y]$;
--   2. $y\mapsto\mathcal B^*_y$ is Lipschitz continuous on $[0,\bar y]$: it is finite there, and for some $L\ge0$,
--   $$|\mathcal B^*_x-\mathcal B^*_y|\le L|x-y|,\qquad x,y\in[0,\bar y];$$
--   3. $\mathcal B^*_y\in(0,\infty)$ for every $y\in[0,\bar y)$.
--
--   Part 3 at $y=0$ gives $\mathcal B^*_0\in(0,\infty)$, which is what makes the rate functions of the main results nondegenerate.
--
--   **Formalization Note** $\mathcal B^*_y$ takes values in $[0,\infty]$. Part 2 is stated as finiteness on $[0,\bar y]$ together with a Lipschitz bound for the real values.
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, pp. 18–19, Proposition 4.1

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_MFGLimit_LDP_LDP
import Definitions.Def_ReflectedRWLDP_SamplePath_PathSpace
import Definitions.Def_ReflectedRWLDP_SamplePath_LDP
import Definitions.Def_ReflectedRWLDP_SamplePath_Model
import Definitions.Def_ReflectedRWLDP_SamplePath_RateFunction

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ReflectedRWLDP.SamplePath

/-- **Proposition 4.1** (pp. 18–19). On `[0, ȳ]`: (i) `y ↦ B*_y` is non-increasing; (ii) it is finite and
Lipschitz continuous; (iii) `B*_y ∈ (0, ∞)` for every `y ∈ [0, ȳ)`. -/
theorem proposition_4_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) :
    AntitoneOn (Bstar P U p) (Icc 0 (ybar P U p)) ∧
    ((∀ y ∈ Icc 0 (ybar P U p), Bstar P U p y ≠ ⊤) ∧
      ∃ L : NNReal, LipschitzOnWith L (fun y => (Bstar P U p y).toReal) (Icc 0 (ybar P U p))) ∧
    ∀ y ∈ Ico 0 (ybar P U p), 0 < Bstar P U p y ∧ Bstar P U p y < ⊤ := by sorry

end ReflectedRWLDP.SamplePath
