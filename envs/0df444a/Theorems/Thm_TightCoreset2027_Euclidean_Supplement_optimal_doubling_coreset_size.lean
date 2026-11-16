-- Prove2me | Theorems.Thm_TightCoreset2027_Euclidean_Supplement_optimal_doubling_coreset_size
-- name    : TightCoreset2027.Euclidean.Supplement.optimal_doubling_coreset_size
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:10:55.705082+00:00
-- url     : https://prove2.me/theorems/a2571bdd-e62e-451b-ae26-312d05c02316
-- title:
--   Theorem 1.4 — optimal worst-case strong coreset size in doubling metrics
-- statement:
--   Fix a real z≥2. There exist c_low,c_up,C>0, 0<ε₀<1 and natural degrees a_low,b_low,a_up,b_up, depending only on z. For every integer k≥1, every 0<ε≤ε₀ and every prescribed real D≥C log(2/ε), put
--
--   $$F=kD\min\{k^{1-2/z}\varepsilon^{-2},\varepsilon^{-z}\},\qquad L_{a,b}=\log(2+k)^a\log(2+1/\varepsilon)^b.$$
--
--   Both of the following hold:
--
--   1. Every finite positively weighted input X in every ambient metric space of doubling dimension at most D admits a strong ε-coreset on its positive support S⊆X with
--
--      $$|S|\le c_{\mathrm{up}}F L_{a_{\mathrm{up}},b_{\mathrm{up}}}.$$
--
--   2. There is a finite ambient metric of doubling dimension at most D and a finite positively weighted input X such that every nonnegatively reweighted strong ε-coreset S⊆X satisfies
--
--      $$|S|\ge c_{\mathrm{low}}F/L_{a_{\mathrm{low}},b_{\mathrm{low}}}.$$
--
--   Strong means preserving the weighted cost of every ambient set of exactly k distinct centers. All constants and log degrees are chosen before k, ε, D, the space, the input and the weights. The upper direction retains arbitrary ambient spaces. The lower direction may be witnessed by a finite metric, as supplied by Lemma 3.1 with all input weights one. The theorem includes z=2, both branches and ε=ε₀. This is a companion theorem to the inherited Euclidean goal; Lemmas 3.1 and 4.1 support this companion, rather than the Euclidean proof.
--
--   Differences from the source:
--   - encoding: optimal worst-case size is Θ̃_z(F) → a uniform existential coreset upper bound for every eligible input together with an existential hard-input lower bound; reason: these are the two directions of worst-case optimal size, avoiding a supremum over metric types; the source supplies a finite lower witness
--   - encoding: polynomial factors in log(2+k) and log(2+1/ε) → separate natural log degrees in each direction, with positive leading constants and thresholds before all varying parameters; reason: footnote 1 permits precisely these factors; each finite polynomial is bounded by a constant times such a monomial on the stated domain
--   - encoding: weighted finite inputs and strong ambient exact-k queries → NNReal weights on Finsets, positive input weights, positive-support upper outputs and an unrestricted nonnegative lower reweighting; reason: ambient extensions ignore weights outside the finite sets, and deleting zero upper weights changes no instance
--   - encoding: ambient doubling dimension at most the real number D → a direct closed-ball covering predicate for arbitrary spaces, with finite lower metrics relabeled as Fin N; reason: this measures the whole ambient space without imposing compactness, completeness or a finite-ambient upper restriction
-- source:
--   Junqiu Hu, Lingxiao Huang, Jian Li, Baoduo Xu, STOC 2027 submission #879 (October 2026), Theorem 1.4, printed p. 3 / PDF p. 5; canonical source.pdf SHA256 9c247b18d4e2080420cb421dad0fe6c53b99885cef599b8f8e3cd8d639e13d5f.

import Definitions.Def_TightCoreset2027_Euclidean_Supplement_weightedCoresets
import Definitions.Def_TightCoreset2027_Euclidean_Supplement_doublingGeometry
import Definitions.Def_TightCoreset2027_Euclidean_Supplement_sizeScales
set_option autoImplicit false
universe uOptimal

namespace TightCoreset2027.Euclidean.Supplement

/-- Theorem 1.4: both directions of the optimal worst-case bound.
Constants and finite log degrees precede every varying parameter and metric input. -/
theorem optimal_doubling_coreset_size (z : ℝ) (hz : 2 ≤ z) :
    ∃ cLower cUpper C ε₀ : ℝ,
      0 < cLower ∧ 0 < cUpper ∧ 0 < C ∧ 0 < ε₀ ∧ ε₀ < 1 ∧
      ∃ aLower bLower aUpper bUpper : ℕ,
      ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ D : ℝ, C * Real.log (2 / ε) ≤ D →
        (∀ (E : Type uOptimal) [MetricSpace E], HasDoublingDimensionAtMost E D →
          ∀ (X : Finset E) (u : E → NNReal), (∀ p ∈ X, 0 < u p) →
          ∃ (S : Finset E) (w : E → NNReal),
            IsWeightedStrongCoreset z ε k X u S w ∧
            (∀ p ∈ S, 0 < w p) ∧
            (S.card : ℝ) ≤ cUpper * doublingSizeScale z k ε D *
              polylogFactor aUpper bUpper k ε) ∧
        (∃ (N : ℕ) (metric : MetricSpace (Fin N)),
          letI : MetricSpace (Fin N) := metric
          HasDoublingDimensionAtMost (Fin N) D ∧
          ∃ (X : Finset (Fin N)) (u : Fin N → NNReal),
            (∀ p ∈ X, 0 < u p) ∧
            ∀ (S : Finset (Fin N)) (w : Fin N → NNReal),
              IsWeightedStrongCoreset z ε k X u S w →
              cLower * doublingSizeScale z k ε D /
                polylogFactor aLower bLower k ε ≤ (S.card : ℝ)) := by sorry

end TightCoreset2027.Euclidean.Supplement
