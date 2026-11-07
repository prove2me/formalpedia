-- Prove2me | Theorems.Thm_PrivBayesTest_proposition_2_3
-- name    : PrivBayesTest.proposition_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:25:07.122985+00:00
-- url     : https://prove2.me/theorems/0148e2aa-f26b-4d9f-95b7-161db36aa3a0
-- title:
--   Proposition 2.3: $F_\alpha$ is concave in $\alpha$ and jointly convex, its minimizer exists, and optimizers balance with a value $\tau$
-- statement:
--   Let $\varepsilon>0$, let $P,Q$ be probability measures on $\mathcal X$ and $F_\alpha(R,S)=\alpha\mathrm{KL}(R\|P)+(1-\alpha)\mathrm{KL}(S\|Q)+\tilde\alpha\varepsilon\mathrm{TV}(R,S)$. Then:
--
--   1. for probability measures $R,S$ with $\mathrm{KL}(R\|P),\mathrm{KL}(S\|Q)<\infty$, the map $\alpha\mapsto F_\alpha(R,S)$ is concave on $(0,1)$, and if one of the two divergences is infinite then $F_\alpha(R,S)=+\infty$ for every $\alpha\in(0,1)$; for every $\alpha\in(0,1)$, $F_\alpha$ is jointly convex: for probability measures $R,S,R',S'$ and $w\in[0,1]$,
--   $$
--   F_\alpha\big((1-w)R+wR',\,(1-w)S+wS'\big)\le(1-w)F_\alpha(R,S)+wF_\alpha(R',S');
--   $$
--   2. for every $\alpha\in(0,1)$ the infimum $\inf_{R,S}F_\alpha(R,S)$ (the right-hand side of display (4)) is attained;
--   3. if $\alpha^*\in(0,1)$ maximizes $\alpha\mapsto\inf_{R,S}F_\alpha(R,S)$ over $(0,1)$ and $(R^*,S^*)$ minimizes $F_{\alpha^*}$, then there is $\tau\in[0,1]$ with
--   $$
--   \mathrm{KL}(R^*\|P)+\tau\varepsilon\mathrm{TV}(R^*,S^*)=\mathrm{KL}(S^*\|Q)+(1-\tau)\varepsilon\mathrm{TV}(R^*,S^*),
--   $$
--   and $\tau\in\{0,1\}$ if $\alpha^*\ne1/2$.
--
--   These structural facts feed the dual representation (Lemma 2.4) and the converse (Lemma 3.2).
--
--   Differences from the source:
--   - encoding: F_α(R, S) is concave in α → concave on (0,1) as a real function when both KL terms are finite; identically +∞ on (0,1) otherwise; reason: an extended-real function equal to +∞ is concave; the two cases cover all pairs
--   - encoding: jointly convex in R, S → the mixture inequality for probability measures, in [0, ∞]; reason: convexity on the convex set of pairs of probability measures
--   - reading: Let R*, S*, α* attain the optimum in the right-hand side of Lemma 2.1 → α* ∈ (0,1) maximizes α ↦ inf_{R,S} F_α and (R*, S*) minimizes F_{α*}; the conclusion for every such triple; reason: the strong reading; it holds because F_{α*} is strictly convex where finite, so its minimizer is the saddle point's
--   - reading: KL(R ∥ P) + τε TV(R, S) = KL(S ∥ Q) + (1 − τ)ε TV(R, S) → the same equation at R*, S*; reason: the printed R, S name the optimizers R*, S* of the preceding sentence
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Proposition 2.3, pp.9–10

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_tvDist
import Definitions.Def_PrivBayesTest_klTvValue

open MeasureTheory

namespace PrivBayesTest

/-- **Proposition 2.3** of Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), pp.9–10. Fix `P, Q` and let
`F_α(R, S) = α KL(R ∥ P) + (1 − α) KL(S ∥ Q) + α̃ ε TV(R, S)`. Then
1. `F_α(R, S)` is concave in `α` and jointly convex in `R, S`;
2. the solution to (4) (the infimum of `F_α` over `R, S`) always exists;
3. if `R*, S*, α*` attain the optimum in the right-hand side of Lemma 2.1, there is `τ ∈ [0,1]` with
   `KL(R* ∥ P) + τ ε TV(R*, S*) = KL(S* ∥ Q) + (1 − τ) ε TV(R*, S*)`, and `τ ∈ {0,1}` if `α* ≠ 1/2`.

**Formalization Note** `α ∈ (0,1)` throughout. Item 1, concavity: for `R, S` with finite KL terms,
`α ↦ F_α(R, S)` is concave on `(0,1)` (as a real function); if a KL term is infinite then
`F_α(R, S) = +∞` for every `α ∈ (0,1)` (the constant `+∞`). Joint convexity is the mixture inequality
for probability measures in `ENNReal`. Item 3 reads "attain the optimum" as: `α*` maximizes
`α ↦ inf_{R,S} F_α` over `(0,1)` and `(R*, S*)` minimizes `F_{α*}`; the conclusion holds for every such
triple. The printed equation writes `R, S` for `R*, S*`. -/
theorem proposition_2_3 {X : Type*} [MeasurableSpace X] (ε : ℝ) (hε : 0 < ε) (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    ((∀ R S : Measure X, IsProbabilityMeasure R → IsProbabilityMeasure S →
        InformationTheory.klDiv R P ≠ ⊤ → InformationTheory.klDiv S Q ≠ ⊤ →
          ConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) (fun α => (klTvObj ε P Q α R S).toReal)) ∧
      (∀ R S : Measure X, IsProbabilityMeasure R → IsProbabilityMeasure S →
        (InformationTheory.klDiv R P = ⊤ ∨ InformationTheory.klDiv S Q = ⊤) →
          ∀ α ∈ Set.Ioo (0 : ℝ) 1, klTvObj ε P Q α R S = ⊤) ∧
      (∀ α ∈ Set.Ioo (0 : ℝ) 1, ∀ R S R' S' : Measure X, IsProbabilityMeasure R →
        IsProbabilityMeasure S → IsProbabilityMeasure R' → IsProbabilityMeasure S' →
          ∀ w ∈ Set.Icc (0 : ℝ) 1,
            klTvObj ε P Q α (ENNReal.ofReal (1 - w) • R + ENNReal.ofReal w • R')
                (ENNReal.ofReal (1 - w) • S + ENNReal.ofReal w • S') ≤
              ENNReal.ofReal (1 - w) * klTvObj ε P Q α R S
                + ENNReal.ofReal w * klTvObj ε P Q α R' S')) ∧
      (∀ α ∈ Set.Ioo (0 : ℝ) 1, ∃ R S : ProbabilityMeasure X,
        klTvObj ε P Q α R S = klTvInf ε P Q α) ∧
      (∀ α₀ ∈ Set.Ioo (0 : ℝ) 1, (∀ α ∈ Set.Ioo (0 : ℝ) 1, klTvInf ε P Q α ≤ klTvInf ε P Q α₀) →
        ∀ R₀ S₀ : ProbabilityMeasure X, klTvObj ε P Q α₀ R₀ S₀ = klTvInf ε P Q α₀ →
          ∃ τ ∈ Set.Icc (0 : ℝ) 1,
            InformationTheory.klDiv (R₀ : Measure X) P
                + ENNReal.ofReal (τ * ε * FoundationsRL.DECLower.tvDist (R₀ : Measure X) (S₀ : Measure X)) =
              InformationTheory.klDiv (S₀ : Measure X) Q
                + ENNReal.ofReal ((1 - τ) * ε * FoundationsRL.DECLower.tvDist (R₀ : Measure X) (S₀ : Measure X)) ∧
            (α₀ ≠ 1 / 2 → τ = 0 ∨ τ = 1)) := by sorry

end PrivBayesTest
