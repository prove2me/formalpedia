-- Prove2me | Theorems.Thm_PrivBayesTest_corollary_C_2
-- name    : PrivBayesTest.corollary_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:24:58.335203+00:00
-- url     : https://prove2.me/theorems/36438964-feb2-4456-bcaf-c9e093623b69
-- title:
--   Corollary C.2: optimizers of the KL–TV problem exist, live in a compact set $K$, and balance with a value $\tau$
-- statement:
--   Let $\varepsilon>0$, let $P\ne Q$ be probability measures on $\mathcal X$, and let $F_\alpha(R,S)=\alpha\mathrm{KL}(R\|P)+(1-\alpha)\mathrm{KL}(S\|Q)+\tilde\alpha\varepsilon\mathrm{TV}(R,S)$. Let
--
--   $$
--   K=\{(R,S)\in\Delta(\mathcal X)^2:\ \mathrm{KL}(R\|P)\le\varepsilon\mathrm{TV}(P,Q),\ \mathrm{KL}(S\|Q)\le\varepsilon\mathrm{TV}(P,Q)\}.
--   $$
--
--   1. For every $\alpha\in[0,1]$ the infimum of $F_\alpha$ over pairs of probability measures is attained, and it equals the infimum over $K$. The set $K$ (which does not depend on $\alpha$) is compact in the topology of setwise convergence.
--   2. There exist $\alpha^*\in(0,1)$, $(R^*,S^*)\in K$ and $\tau\in[0,1]$ such that $(R^*,S^*)$ minimizes $F_{\alpha^*}$ over all pairs, $\alpha^*$ maximizes $\alpha\mapsto F_\alpha(R^*,S^*)$ over $[0,1]$, $\tau\in\{0,1\}$ if $\alpha^*\ne1/2$, and
--   $$
--   \mathrm{KL}(R^*\|P)+\tau\varepsilon\mathrm{TV}(R^*,S^*) \;=\; \mathrm{KL}(S^*\|Q)+(1-\tau)\varepsilon\mathrm{TV}(R^*,S^*) \;=\; \sup_{\alpha\in(0,1)}\inf_{R,S}F_\alpha(R,S).
--   $$
--
--   The pair $(R^*,S^*)$ and the value $\tau$ build the intermediate mixture $(1-\tau)R^*+\tau S^*$ of the converse proof (Lemma 3.2).
--
--   Differences from the source:
--   - reading: K … is compact → the image of K under (R, S) ↦ (A ↦ R(A), A ↦ S(A)) (A measurable) is compact in the product topology, i.e. K is compact for setwise convergence; reason: the paper's spaces of measures carry no other topology
--   - generalization: for every α → for every α ∈ [0, 1]; reason: the range of α in Lemma C.1, which the corollary applies, is [0, 1]; it contains α ∈ (0, 1), the range of F_α in Theorem 1.3 and Lemma 2.1
--   - reading: (R*, S*) and α* forming a saddle point of F → (R*, S*) minimizes F_{α*} over all pairs of probability measures and α* maximizes α ↦ F_α(R*, S*) over [0, 1]; reason: the saddle-point notion of Lemma C.1, applied with ω = α̃
--   - encoding: K does not depend on α → K is written without α; reason: holds by construction
--   - encoding: real-valued exponents, divergences and suprema → extended reals (EReal/ENNReal) with −log 0 = +∞; reason: Lean convention; avoids junk values of real sup/inf; same instances
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Corollary C.2, p.29

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_tvDist
import Definitions.Def_PrivBayesTest_klTvValue

open MeasureTheory

namespace PrivBayesTest

/-- **Corollary C.2 (Optimizers of the KL–TV Problem)** of Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), p.29. Fix `P ≠ Q` and let
`F_α(R, S) = α KL(R ∥ P) + (1 − α) KL(S ∥ Q) + α̃ ε TV(R, S)`.
1. For every `α`, the infimum of `F_α` over `R, S` is attained, and it suffices to optimize over
   `K = {(R, S) | KL(R ∥ P), KL(S ∥ Q) ≤ ε TV(P, Q)}`, which is compact and does not depend on `α`.
2. There exist `α* ∈ (0,1)` and `(R*, S*) ∈ K` forming a saddle point of `F`, and `τ ∈ [0,1]`, with
   `τ ∈ {0,1}` if `α* ≠ 1/2`, such that
   `KL(R* ∥ P) + τ ε TV(R*, S*) = KL(S* ∥ Q) + (1 − τ) ε TV(R*, S*) = sup_{α∈(0,1)} inf_{R,S} F_α(R, S)`.

**Formalization Note** `R, S` range over probability measures on `X`; `α` over `[0,1]` in item 1 (the range of `α` in Lemma C.1, which this corollary applies; it contains the `(0,1)` of Theorem 1.3, and at `α ∈ {0,1}` the weight `α̃` vanishes).
"Compact" is compactness in the topology of setwise convergence, the coarsest topology making every
`R ↦ R(A)` (`A` measurable) continuous: `K` is mapped to `(A ↦ R(A), A ↦ S(A))` in the product
topology and its image is compact. "Saddle point of `F`" means `(R*, S*)` minimizes `F_{α*}` over all
pairs and `α*` maximizes `α ↦ F_α(R*, S*)` over `[0,1]`. The equalities are in `ENNReal` and `EReal`. -/
theorem corollary_C_2 {X : Type*} [MeasurableSpace X] (ε : ℝ) (hε : 0 < ε) (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≠ Q) :
    (∀ α ∈ Set.Icc (0 : ℝ) 1,
        (∃ R S : ProbabilityMeasure X, klTvObj ε P Q α R S = klTvInf ε P Q α) ∧
        (⨅ (RS : ProbabilityMeasure X × ProbabilityMeasure X)
            (_ : InformationTheory.klDiv (RS.1 : Measure X) P
                ≤ ENNReal.ofReal (ε * FoundationsRL.DECLower.tvDist P Q) ∧
              InformationTheory.klDiv (RS.2 : Measure X) Q
                ≤ ENNReal.ofReal (ε * FoundationsRL.DECLower.tvDist P Q)),
            klTvObj ε P Q α RS.1 RS.2) = klTvInf ε P Q α) ∧
      IsCompact ((fun RS : ProbabilityMeasure X × ProbabilityMeasure X =>
          ((fun A : {A : Set X // MeasurableSet A} => (RS.1 : Measure X) A.1),
            (fun A : {A : Set X // MeasurableSet A} => (RS.2 : Measure X) A.1))) ''
        {RS | InformationTheory.klDiv (RS.1 : Measure X) P
                ≤ ENNReal.ofReal (ε * FoundationsRL.DECLower.tvDist P Q) ∧
              InformationTheory.klDiv (RS.2 : Measure X) Q
                ≤ ENNReal.ofReal (ε * FoundationsRL.DECLower.tvDist P Q)}) ∧
      ∃ α₀ ∈ Set.Ioo (0 : ℝ) 1, ∃ R₀ S₀ : ProbabilityMeasure X,
        InformationTheory.klDiv (R₀ : Measure X) P
            ≤ ENNReal.ofReal (ε * FoundationsRL.DECLower.tvDist P Q) ∧
        InformationTheory.klDiv (S₀ : Measure X) Q
            ≤ ENNReal.ofReal (ε * FoundationsRL.DECLower.tvDist P Q) ∧
        (∀ R S : ProbabilityMeasure X, klTvObj ε P Q α₀ R₀ S₀ ≤ klTvObj ε P Q α₀ R S) ∧
        (∀ α ∈ Set.Icc (0 : ℝ) 1, klTvObj ε P Q α R₀ S₀ ≤ klTvObj ε P Q α₀ R₀ S₀) ∧
        ∃ τ ∈ Set.Icc (0 : ℝ) 1, (α₀ ≠ 1 / 2 → τ = 0 ∨ τ = 1) ∧
          InformationTheory.klDiv (R₀ : Measure X) P
              + ENNReal.ofReal (τ * ε * FoundationsRL.DECLower.tvDist (R₀ : Measure X) (S₀ : Measure X)) =
            InformationTheory.klDiv (S₀ : Measure X) Q
              + ENNReal.ofReal ((1 - τ) * ε * FoundationsRL.DECLower.tvDist (R₀ : Measure X) (S₀ : Measure X)) ∧
          ((InformationTheory.klDiv (R₀ : Measure X) P
              + ENNReal.ofReal (τ * ε * FoundationsRL.DECLower.tvDist (R₀ : Measure X) (S₀ : Measure X)) : ENNReal) : EReal) =
            klTvValue ε P Q := by sorry

end PrivBayesTest
