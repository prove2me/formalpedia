-- Prove2me | Theorems.Thm_ValiantModel_Supplement_theorem_A_1
-- name    : ValiantModel.Supplement.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:25:13.232809+00:00
-- url     : https://prove2.me/theorems/3a50d63e-5369-41e6-a510-aa931a52bc4e
-- title:
--   Theorem A.1, p.50 — intersections of $s$ halfspaces are learnable in Valiant's model (corrected: $\log(2/\delta)$)
-- statement:
--   There is an absolute constant $C>0$ such that for all $d,s\ge1$, the class of intersections of $s$ halfspaces in $\mathbb R^d$ is learnable in Valiant's model over $\mathbb R^d$ (Definition 3) by a learner with sample complexity $m(\varepsilon,\delta)$ and query complexity $q(\varepsilon,\delta)$ satisfying, for all $\varepsilon,\delta\in(0,1)$,
--   $$m(\varepsilon,\delta)\le C\,\frac{s\,d^2\log_2(sd)\cdot\log_2(1/\varepsilon)+\log_2(2/\delta)}{\varepsilon},\qquad q(\varepsilon,\delta)\le (2es)^d\,m(\varepsilon,\delta)^{s(d^2+1)} .$$
--
--   This extends Theorem 1.6 from one halfspace to polytopes with at most $s$ facets.
--
--   Differences from the source:
--   - correction: log(1/δ) in m(ε, δ) → log₂(2/δ); reason: the printed bound tends to 0 as ε, δ → 1 (and as δ → 1 for every ε when d = s = 1), forcing no examples and hence no queries, which fails: with the halfspaces {x₁ ≥ c}, c ∈ ℕ (each an intersection of s copies of itself), and D_c the point mass at c·e₁, the success events are disjoint in c, so a learner without information succeeds with probability 0 < 1 − δ on some target
--   - encoding: O(·) → one absolute constant `C > 0` quantified before d and s; the learner may depend on d and s; reason: the proof's constants are uniform in d and s
--   - encoding: q(ε, δ) = (2es)^d m^{s(d²+1)} → an upper bound with m the example budget of the same learner and e = `Real.exp 1`; reason: the query complexity is a bound on the number of queries (Lemma A.7: 'at most')
--   - encoding: log → `Real.logb 2`; reason: logarithms are base two (§3, p.14)
--   - encoding: ℝ^d with every distribution → `Fin d → ℝ` with its Borel σ-algebra and every Borel probability measure; compatibility almost surely, the error by the outer measure; reason: the standard measurable structure of ℝ^d; continuous distributions included
--   - encoding: a randomized learner → `RandProtocol`: an arbitrary probability space of internal randomness and a deterministic `GProtocol` for each value, success probability by the lower Lebesgue integral; reason: this is exact whenever the success event is measurable, and the paper's probability is defined only then; examples and queries interleave, queries may be asked anywhere, and outputs are improper
--   - encoding: intersections of s halfspaces → indicators of ⋂_{t < s} P t with each P t an `IsHalfspace` set; reason: repetitions are allowed, as on p.50
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), Theorem A.1, p.50 (PDF p.52); proof pp.50–52 (PDF pp.52–54)

import Mathlib
import Definitions.Def_ValiantModel_Supplement_GeneralModel
import Definitions.Def_ValiantModel_Supplement_Halfspaces

namespace ValiantModel.Supplement

/-- **Theorem A.1 (Intersections of Halfspaces Are Learnable in Valiant's Model)**, Hanneke, Mehrotra,
Velegkas, Zampetakis, arXiv:2605.13840 (version held, sha256 f793f255…), p.50 (PDF p.52): for
`d, s ≥ 1`, intersections of `s` halfspaces in `ℝ^d` are learnable in Valiant's model over `ℝ^d`
(Definition 3) with sample complexity `m(ε, δ) ≤ C (s d² log(sd) · log(1/ε) + log(2/δ)) / ε` and query
complexity `q(ε, δ) ≤ (2es)^d · m(ε, δ)^{s(d²+1)}`.

**Formalization Note.** `O(·)` is one absolute constant `C`, the same for all `d, s`; the learner may
depend on `d, s`. The query bound is exact, with `m(ε, δ)` the example budget of the same learner and
`e = exp 1`. Logarithms are base two. Corrected: the printed `log(1/δ)` is `log(2/δ)` here; the printed
sample bound tends to `0` as `ε, δ → 1` (and for every `ε` at `d = s = 1`), while no learner without
examples succeeds (halfspaces `{x₁ ≥ c}`, `c ∈ ℕ`, point masses at `c e₁`). `ℝ^d` is `Fin d → ℝ` with
its Borel σ-algebra. -/
theorem theorem_A_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ d s : ℕ, 1 ≤ d → 1 ≤ s →
      ∃ (L : ℝ → ℝ → RandProtocol (Fin d → ℝ)) (m q : ℝ → ℝ → ℕ),
        GHasComplexity (halfspaceIntersections d s) L m q ∧
        ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
          (m ε δ : ℝ) ≤ C * ((s : ℝ) * (d : ℝ) ^ 2 * Real.logb 2 ((s : ℝ) * d) *
            Real.logb 2 (1 / ε) + Real.logb 2 (2 / δ)) / ε ∧
          (q ε δ : ℝ) ≤ (2 * Real.exp 1 * s) ^ d * (m ε δ : ℝ) ^ (s * (d ^ 2 + 1)) := by sorry

end ValiantModel.Supplement
