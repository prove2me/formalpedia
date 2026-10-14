-- Prove2me | Theorems.Thm_UnknownLoads_Refined_lemma_6
-- name    : UnknownLoads.Refined.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:34:34.201962+00:00
-- url     : https://prove2.me/theorems/e23fc8ec-d552-4a4b-aa1f-053f5f861b1d
-- title:
--   Lemma 6 — sup_{t∈[0,T]} n^γ |𝒩(nt)/n − t| → 0 almost surely for all γ ∈ [0, 1/2)
-- statement:
--   Let $\mathcal N$ be a unit-rate Poisson process on $(\Omega,\mathcal F,\mathbb P)$ and $T\in\mathbb R$. Then with probability one
--   $$
--   \lim_{n\to\infty}\sup_{t\in[0,T]}n^\gamma\Big|\frac{\mathcal N(nt)}{n}-t\Big|=0\qquad\text{for all }\gamma\in[0,1/2).
--   $$
--
--   This refines the functional strong law of large numbers for the Poisson process with a rate $n^{-\gamma}$; it yields (12b) and (12c) of Proposition 7.
--
--   **Formalization Note** The Poisson process is the published `BesbesZeevi.Parametric.PoissonProcess`. The set of probability one does not depend on $\gamma$. The limit is written in $\varepsilon$–$n$ form: for every $\varepsilon>0$, eventually in $n$, the bound $\le\varepsilon$ holds for all $t\in[0,T]$.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, p. 27, Lemma 6 (proof in App. B, pp. 48–49)

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_PoissonProcess

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace UnknownLoads.Refined

theorem lemma_6 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (N : BesbesZeevi.Parametric.PoissonProcess Ω P) (T : ℝ) :
    ∀ᵐ ω ∂P, ∀ γ ∈ Ico (0 : ℝ) (1 / 2), ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ t ∈ Icc 0 T,
      (n : ℝ) ^ γ * |(N.count ((n : ℝ) * t) ω : ℝ) / n - t| ≤ ε := by sorry

end UnknownLoads.Refined
