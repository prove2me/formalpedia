-- Prove2me | Theorems.Thm_ValiantModel_Supplement_theorem_1_5
-- name    : ValiantModel.Supplement.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:23:05.016317+00:00
-- url     : https://prove2.me/theorems/9896b470-f3bb-44b6-af36-1f34fcd70c64
-- title:
--   Theorem 1.5, p.5 — sandwich between PAC and positive-only learning over a general domain
-- statement:
--   Fix a domain $X$, a concept class $H\subseteq\{0,1\}^X$, and let $\overline H$ be its intersection closure. In Valiant's model over a general domain (Definition 3):
--
--   1. If $H$ is learnable with $m(\varepsilon,\delta)$ positive examples and membership queries, then
--   $$\mathrm{VC}(H)\le 9\,m(1/3,1/3)+1 .$$
--   2. If $|X|=\infty$, $H$ contains the constant-one hypothesis, and for every $x\in X$ it contains the hypothesis that labels $x$ zero and every point of $X\setminus\{x\}$ one, then $H$ is not learnable. In particular, there exists a class $H$ with $\mathrm{VC}(H)=1$ that is not learnable.
--   3. If $\mathrm{VC}(\overline H)<\infty$, then $H$ is learnable with sample and query complexity
--   $$m(\varepsilon,\delta)\le C\,\frac{\mathrm{VC}(\overline H)\,\log_2(2/\varepsilon)+\log_2(1/\delta)}{\varepsilon},$$
--   where $C$ is an absolute constant. This explicit form implies the printed $\tilde O\big((1/\varepsilon)(\mathrm{VC}(\overline H)+\log(1/\delta))\big)$.
--
--   The theorem places Valiant's model strictly between PAC learning (item 1) and positive-only learning (item 3), and item 2 shows that the first inclusion is strict.
--
--   Differences from the source:
--   - reading: Õ((1/ε)(VC(H̄) + log 1/δ)) → C (VC(H̄) log₂(2/ε) + log₂(1/δ)) / ε with one absolute C; reason: the explicit bound of the proof (Theorem 5.2(3) with s₁(H) ≤ VC(H̄)), which implies the Õ bound; log₂(2/ε) keeps the bound ≥ C/ε when VC(H̄) ≥ 1, and VC(H̄) = 0 forces |H| ≤ 1
--   - encoding: O(·) → one absolute constant `C > 0` quantified before the domain and the class; reason: O(·) is uniform in the class
--   - encoding: log → `Real.logb 2`; reason: logarithms are base two (§3, p.14)
--   - reading: every distribution D over X → every probability measure on X with the discrete σ-algebra (`DiscreteMeasurableSpace`), with compatibility almost surely and the error by the outer measure; reason: the paper fixes no σ-algebra (§3, p.14, a probability mass function when X is countable, arbitrary probability measures when X is uncountable) and states no measurability condition for the events it writes; with all subsets measurable every concept and every output is an event; on countable X these are exactly the paper's distributions, on uncountable X they are the probability measures defined on all subsets
--   - encoding: a randomized learner → `RandProtocol`: an arbitrary probability space of internal randomness and a deterministic `GProtocol` for each value, success probability by the lower Lebesgue integral; reason: this is exact whenever the success event is measurable, and the paper's probability is defined only then; examples and queries interleave, queries may be asked anywhere, and outputs are improper
--   - encoding: learnable with m(ε, δ) positive examples/membership queries → `GHasComplexity H L m m`: at most m(ε, δ) calls on each oracle on every path, for every value of the randomness, for ε, δ ∈ (0,1); reason: the paper's count (proof of Theorem 5.2, p.34: budget M for each oracle)
--   - encoding: VC(H) and VC(H̄) → the ℕ∞-valued published `vcDim`; VC(H̄) < ∞ is `< ⊤` and its value in the bound is `toNat`; reason: the finite value is the integer VC dimension
--   - generalization: there exists H with VC(H) = 1 that is not learnable → there exist a countable X with the discrete σ-algebra and H ⊆ {0,1}^X with VC(H) = 1 that is not learnable; reason: a more specific witness implies the source's clause; the paper's witness is on ℤ
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), Theorem 1.5, p.5 (PDF p.7); restated pp.33–34 (PDF pp.35–36); proof §5.3 via Theorem 5.2

import Mathlib
import Definitions.Def_HighDimProb_Chaining_VcDim
import Definitions.Def_ValiantModel_Supplement_GeneralModel
import Definitions.Def_ValiantModel_Supplement_IntersectionClosure

open HighDimProb.Chaining

namespace ValiantModel.Supplement

/-- **Theorem 1.5 (Sandwich between PAC and Positive-Only Learning)**, Hanneke, Mehrotra, Velegkas,
Zampetakis, arXiv:2605.13840 (version held, sha256 f793f255…), p.5 (PDF p.7), restated p.33–34 (PDF
pp.35–36), in Valiant's model over a general domain (Definition 3), with `H̄` the intersection closure:
1. if a learner learns `H` with `m(ε, δ)` examples and queries, then `VC(H) ≤ 9 m(1/3, 1/3) + 1`;
2. if `X` is infinite, `H` contains the constant-one hypothesis and, for every `x`, the hypothesis that
   is `0` exactly at `x`, then `H` is not learnable; and some `H` with `VC(H) = 1` is not learnable;
3. if `VC(H̄) < ∞`, then `H` is learnable with sample and query complexity
   `C (VC(H̄) log(2/ε) + log(1/δ)) / ε`.

**Formalization Note.** `O(·)` is one absolute constant `C`, quantified before the domain and the
class. Item 3's `Õ((1/ε)(VC(H̄) + log 1/δ))` is stated in the explicit form of the proof
(Theorem 5.2(3) with `s₁(H) ≤ VC(H̄)`), which implies the `Õ` bound; `log(2/ε)` keeps the bound
`≥ C / ε` whenever `VC(H̄) ≥ 1`, and `VC(H̄) = 0` forces `|H| ≤ 1`. Logarithms are base two. Domains carry the discrete σ-algebra; the witness of item 2's
last clause is required to be countable, where these measures are exactly the distributions
(probability mass functions) of §3. -/
theorem theorem_1_5 :
    ∃ C : ℝ, 0 < C ∧
      (∀ (X : Type) [MeasurableSpace X] [DiscreteMeasurableSpace X] (H : Set (X → Bool)),
        (∀ (L : ℝ → ℝ → RandProtocol X) (m : ℝ → ℝ → ℕ), GHasComplexity H L m m →
          vcDim H ≤ 9 * ((m (1 / 3) (1 / 3) : ℕ) : ℕ∞) + 1) ∧
        (Infinite X → (fun _ => true) ∈ H → (∀ x : X, ∃ h ∈ H, ∀ y, h y = true ↔ y ≠ x) →
          ¬ GLearnable H) ∧
        (vcDim (intersectionClosure H) < ⊤ →
          ∃ (L : ℝ → ℝ → RandProtocol X) (m : ℝ → ℝ → ℕ), GHasComplexity H L m m ∧
            ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
              (m ε δ : ℝ) ≤ C * (((vcDim (intersectionClosure H)).toNat : ℝ) *
                Real.logb 2 (2 / ε) + Real.logb 2 (1 / δ)) / ε)) ∧
      (∃ (X : Type) (_ : MeasurableSpace X), DiscreteMeasurableSpace X ∧ Countable X ∧
        ∃ H : Set (X → Bool), vcDim H = 1 ∧ ¬ GLearnable H) := by sorry

end ValiantModel.Supplement
