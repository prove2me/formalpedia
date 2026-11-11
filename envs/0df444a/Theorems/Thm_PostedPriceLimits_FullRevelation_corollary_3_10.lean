-- Prove2me | Theorems.Thm_PostedPriceLimits_FullRevelation_corollary_3_10
-- name    : PostedPriceLimits.FullRevelation.corollary_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:29.165902+00:00
-- url     : https://prove2.me/theorems/76bd8e84-7633-4bdd-985a-f8500e3a7ff8
-- title:
--   Corollary 3.10 — concentration of averages over a Bernoulli subset
-- statement:
--   Let $\Omega$ be a finite set and let $S\subseteq\Omega$ be sampled by including each $x\in\Omega$ independently with probability $q\in[0,1]$. Then for every $f:\Omega\to[0,1]$, every $s\in\mathbb N$ and every $t>0$,
--   $$\Pr\Big[|S|\ge s,\ \big|\mathrm{Avg}[f\mid S]-\mathrm{Avg}[f\mid\Omega]\big|\ge t\Big]\le2e^{-2st^2}.$$
--   Here $\mathrm{Avg}[f\mid S]=|S|^{-1}\sum_{x\in S}f(x)$ and $\mathrm{Avg}[f\mid\varnothing]=0$; the event is the joint event, not a conditional one.
--
--   It is the concentration tool behind Propositions A.2 and A.3: the rank sets of §5 are Bernoulli subsets of earlier ones.
--
--   **Formalization Note** The random subset is $\{x: U_x<q\}$ for independent uniform labels $U_x\in[0,1]$.
--
--   Differences from the source:
--   - generalization: s ∈ [|Ω|] as in Theorem 3.9 (the corollary leaves the range of s implicit) → every s ∈ ℕ; reason: for s = 0 the bound is 2 ≥ 1 and for s > |Ω| the event is empty, so the statement contains the source's range
--   - encoding: S includes each item independently w.p. q → S = {x | U_x < q} for independent Unif[0,1] labels; reason: same law of S
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), Corollary 3.10 and Theorem 3.9, p.6 (PDF 7); PDF SHA-256 5be77a250fd554b42d30cff15c46dafe3e43c75a2d90968fae98c61ff1113bb3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1596.pdf

import Mathlib
import Definitions.Def_PostedPriceLimits_FullRevelation_Prelim
open MeasureTheory

namespace PostedPriceLimits.FullRevelation

/-- Corollary 3.10. Let `S ⊆ Ω` contain each `x ∈ Ω` independently with probability `q`.
Then for every `f : Ω → [0,1]`, every `s ∈ ℕ` and every `t > 0`,
`Pr[|S| ≥ s, |Avg[f | S] − Avg[f | Ω]| ≥ t] ≤ 2 e^{−2 s t²}`. -/
theorem corollary_3_10 {Ω : Type*} [Fintype Ω] (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (f : Ω → ℝ) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (s : ℕ) (t : ℝ) (ht : 0 < t) :
    (subsetLabelLaw Ω).real {U | s ≤ (sampledSubset q U).card ∧
        t ≤ |avg (sampledSubset q U) f - avg Finset.univ f|} ≤
      2 * Real.exp (-2 * s * t ^ 2) := by sorry

end PostedPriceLimits.FullRevelation
