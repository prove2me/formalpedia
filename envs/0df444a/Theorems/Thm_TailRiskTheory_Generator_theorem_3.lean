-- Prove2me | Theorems.Thm_TailRiskTheory_Generator_theorem_3
-- name    : TailRiskTheory.Generator.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:57.827588+00:00
-- url     : https://prove2.me/theorems/49a6d46f-418b-4e93-a11f-746fd70bb243
-- title:
--   Theorem 3, p. 10 — worst-case aggregation of a monotone p-tail risk measure equals that of its generator over the tail marginals
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, $p\in(0,1)$, and let $(\rho,\rho^*)$ be a $p$-tail pair on $L^\infty$ with both $\rho$ and $\rho^*$ monotone. Let $F_1,\dots,F_n$ be distributions of random variables $X_1,\dots,X_n\in L^\infty$, and let $F_i^{[p]}$ be the $p$-tail distribution of $F_i$, the law of $(X_i)_p$. Then
--   $$\sup\{\rho(S):S\in\mathcal S_n(F_1,\dots,F_n)\}=\sup\{\rho^*(T):T\in\mathcal S_n(F_1^{[p]},\dots,F_n^{[p]})\}, \tag{7}$$
--   where $\mathcal S_n(G_1,\dots,G_n)=\{Y_1+\dots+Y_n: Y_i\in L^\infty,\ Y_i\sim G_i\}$ is the aggregation set.
--
--   The worst-case value of a tail risk measure over all dependence structures with given marginals equals the worst-case value of its generator over the tail marginals; this is the step that completes the proof of Theorem 1 (iii).
--
--   **Formalization Note** The space of risks is $L^\infty$, and each $F_i$ is given by a representative $X_i\in L^\infty$ (the paper's "compatible with random variables in $\mathcal X$"). Both suprema are taken in the extended reals, so neither side can take a junk value.
-- source:
--   Liu and Wang, A Theory for Measures of Tail Risk, SSRN 2841909 (journal accepted version, Feb 19, 2020), p. 10, Theorem 3, Eq. (7)

import Mathlib
import Definitions.Def_TailRiskTheory_Generator_Model

namespace TailRiskTheory.Generator

open MeasureTheory ProbabilityTheory
open TailRiskSharing.VaRConv (distFn IsAtomless)
open TailRiskSharing.VaRTail (IsMonotone IsTranslationInvariant IsMonetary IsLawInvariant)
open TailRiskSharing.TailConv (Linf)

/-- Theorem 3, p. 10: for a `p`-tail pair `(ρ, ρ^*)` of monotone risk measures and any distributions
`F_1, …, F_n` (the laws of `Xs 1, …, Xs n ∈ 𝒳`),
`sup {ρ(S) : S ∈ S_n(F_1, …, F_n)} = sup {ρ^*(T) : T ∈ S_n(F_1^[p], …, F_n^[p])}` (7). -/
theorem theorem_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : IsAtomless P) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (rho rhoStar : (Ω → ℝ) → ℝ) (hpair : IsPTailPair P p rho rhoStar)
    (hmono : IsMonotone P (Linf P) rho) (hmonoStar : IsMonotone P (Linf P) rhoStar)
    (n : ℕ) (Xs : Fin n → Ω → ℝ) (hXs : ∀ i, Xs i ∈ Linf P) :
    (⨆ S ∈ AggSet P Xs, (rho S : EReal)) = ⨆ T ∈ TailAggSet P p Xs, (rhoStar T : EReal) := by sorry

end TailRiskTheory.Generator
