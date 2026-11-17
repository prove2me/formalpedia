-- Prove2me | Theorems.Thm_ValiantModel_Supplement_theorem_5_2
-- name    : ValiantModel.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:24:16.460006+00:00
-- url     : https://prove2.me/theorems/3c635b8e-08fb-41ed-a5b4-22f711302d85
-- title:
--   Theorem 5.2, p.34 — VC lower bound, whole-domain 1-star obstruction, $s_1$ upper bound (corrected: $\log(2/\delta)$)
-- statement:
--   There is an absolute constant $C>0$ such that, for every domain $X$ and every class $H\subseteq\{0,1\}^X$, in Valiant's model over a general domain (Definition 3):
--
--   1. If $H$ is learnable, witnessed by a learner with complexity $m(\varepsilon,\delta)$, then $\mathrm{VC}(H)\le 9\,m(1/3,1/3)+1$.
--   2. If $|X|=\infty$ and $X$ is a 1-star for $H$, then $H$ is not learnable.
--   3. If $s_1(H)<\infty$, then $H$ is learnable with
--   $$m(\varepsilon,\delta)\le C\,\frac{s_1(H)\log_2(1/\varepsilon)+\log_2(2/\delta)}{\varepsilon}.$$
--
--   This is the star-number form of Theorem 1.5.
--
--   Differences from the source:
--   - correction: log(1/δ) → log₂(2/δ); reason: the printed bound tends to 0 as ε, δ → 1, forcing no examples and no queries, which fails: on X = ℕ the chain h_n = [n, ∞) has s₁ = 1, and with D_n the point mass at n success on (h_n, D_n) requires n ∈ supp g ⊆ [n, ∞), these events are disjoint in n, so a learner without information succeeds with probability 0 < 1 − δ on some target; log₂(2/δ) agrees with the printed form up to the constant for δ ≤ 1/2
--   - encoding: O(·) → one absolute constant `C > 0` quantified before the domain and the class; reason: O(·) is uniform in the class
--   - encoding: log → `Real.logb 2`; reason: logarithms are base two (§3, p.14)
--   - reading: every distribution D over X → every probability measure on X with the discrete σ-algebra (`DiscreteMeasurableSpace`), with compatibility almost surely and the error by the outer measure; reason: the paper fixes no σ-algebra (§3, p.14, a probability mass function when X is countable, arbitrary probability measures when X is uncountable) and states no measurability condition for the events it writes; with all subsets measurable every concept and every output is an event; on countable X these are exactly the paper's distributions, on uncountable X they are the probability measures defined on all subsets
--   - encoding: a randomized learner → `RandProtocol`: an arbitrary probability space of internal randomness and a deterministic `GProtocol` for each value, success probability by the lower Lebesgue integral; reason: this is exact whenever the success event is measurable, and the paper's probability is defined only then; examples and queries interleave, queries may be asked anywhere, and outputs are improper
--   - encoding: learnable with m(ε, δ) positive examples/membership queries → `GHasComplexity H L m m`: at most m(ε, δ) calls on each oracle on every path, for every value of the randomness, for ε, δ ∈ (0,1); reason: the paper's count (proof of Theorem 5.2, p.34: budget M for each oracle)
--   - encoding: VC(H), s₁(H) → ℕ∞-valued `vcDim` and `oneStarNumber`; s₁(H) < ∞ is `< ⊤` and its value in the bound is `toNat`; reason: finite values are the integers of Definitions 9 and 11; for H = ∅ the Lean value 0 replaces an undefined 'largest k', and item 3 is then trivial either way
--   - encoding: X is a 1-star for H → `IsStarSet H (fun _ => true) Set.univ`; reason: Definition 10 centered at the constant-one function with all of X as the point set
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), Theorem 5.2, p.34 (PDF p.36); proof pp.34–35 (PDF pp.36–37)

import Mathlib
import Definitions.Def_HighDimProb_Chaining_VcDim
import Definitions.Def_ValiantModel_Supplement_GeneralModel
import Definitions.Def_ValiantModel_Supplement_StarNumber

open HighDimProb.Chaining

namespace ValiantModel.Supplement

/-- **Theorem 5.2**, Hanneke, Mehrotra, Velegkas, Zampetakis, arXiv:2605.13840 (version held, sha256
f793f255…), p.34 (PDF p.36), in Valiant's model over a general domain (Definition 3):
1. if a learner learns `H` with `m(ε, δ)` examples and queries, then `VC(H) ≤ 9 m(1/3, 1/3) + 1`;
2. if `X` is infinite and `X` is a 1-star for `H`, then `H` is not learnable;
3. if `s₁(H) < ∞`, then `H` is learnable with `m(ε, δ) ≤ C (s₁(H) log(1/ε) + log(2/δ)) / ε`.

**Formalization Note.** `O(·)` is one absolute constant `C`, quantified before the domain and the
class. Logarithms are base two (§3, p.14). Corrected: the printed `log(1/δ)` is `log(2/δ)` here; the
printed bound tends to `0` as `ε, δ → 1` while no learner without examples succeeds (chain
`[n, ∞) ∩ ℕ` on `ℕ`, `s₁ = 1`, point masses). The domain carries the discrete σ-algebra, so every
probability measure on all subsets of `X` is a distribution. `VC(H)` and `s₁(H)` are `ℕ∞`-valued. -/
theorem theorem_5_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : Type) [MeasurableSpace X] [DiscreteMeasurableSpace X] (H : Set (X → Bool)),
        (∀ (L : ℝ → ℝ → RandProtocol X) (m : ℝ → ℝ → ℕ), GHasComplexity H L m m →
          vcDim H ≤ 9 * ((m (1 / 3) (1 / 3) : ℕ) : ℕ∞) + 1) ∧
        (Infinite X → IsStarSet H (fun _ => true) Set.univ → ¬ GLearnable H) ∧
        (oneStarNumber H < ⊤ →
          ∃ (L : ℝ → ℝ → RandProtocol X) (m : ℝ → ℝ → ℕ), GHasComplexity H L m m ∧
            ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
              (m ε δ : ℝ) ≤ C * (((oneStarNumber H).toNat : ℝ) * Real.logb 2 (1 / ε) +
                Real.logb 2 (2 / δ)) / ε) := by sorry

end ValiantModel.Supplement
