-- Prove2me | Theorems.Thm_ValiantModel_Supplement_theorem_A_8
-- name    : ValiantModel.Supplement.theorem_A_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:25:53.53408+00:00
-- url     : https://prove2.me/theorems/c47fdf99-252a-4d00-801a-0909e0b71bb7
-- title:
--   Theorem A.8, p.52 — learnability in Valiant's model is closed under unions
-- statement:
--   Let $H=(H_1,H_2,\dots)$ and $G=(G_1,G_2,\dots)$ be sequences of concept classes, $H_d,G_d\subseteq\{0,1\}^{\{0,1\}^d}$.
--
--   1. If $H$ and $G$ are learnable in Valiant's model (Definition 1), then so is their union $H\cup G:=(H_1\cup G_1,H_2\cup G_2,\dots)$.
--   2. More precisely, there is an absolute constant $C>0$ with the following property. If for every $d\ge1$ every realizable positive sample $S\subseteq\{0,1\}^d$ has a query compression scheme of size at most $q_H(d)$ for $H_d$ and one of size at most $q_G(d)$ for $G_d$, then there is a learner for $H\cup G$ that, for every $d\ge1$ and $\varepsilon,\delta\in(0,1)$, uses at most
--   $$C\,\frac{d\,\big(q_H(d)+q_G(d)\big)+\log_2(1/\delta)}{\varepsilon}\ \text{examples}\qquad\text{and}\qquad q_H(d)+q_G(d)\ \text{membership queries},$$
--   and meets the Valiant guarantee for $H_d\cup G_d$.
--
--   By Theorem 1.1, the quantitative part yields the qualitative one.
--
--   Differences from the source:
--   - generalization: H and G learnable, and H_d, G_d admit schemes of size q_H(d), q_G(d) → the quantitative sentence assumes only the schemes; reason: its proof does not use learnability; under the source's hypotheses it is the source's sentence
--   - encoding: H_d admits query compression schemes of size q_H(d) → `IsCompressionRate (H d) (fun _ => qH d)` for every d ≥ 1 (and the same for G); reason: Definition 15 with a constant rate: every S with V(S) ≠ ∅ has a scheme of depth ≤ q_H(d)
--   - encoding: O(·) → one absolute constant `C > 0` quantified before H, G, q_H, q_G; reason: O(·) is uniform in the classes and d
--   - encoding: a learner that uses at most … examples and … membership queries → the base mission's `Learner`, with the example and query counts bounded separately on every path of every protocol in its support, together with `Guarantee (H d ∪ G d)`; reason: the base mission's model of a randomized learner (a PMF over deterministic protocols)
--   - encoding: log → `Real.logb 2`; reason: logarithms are base two (§3, p.14)
--   - encoding: every d → `1 ≤ d`; reason: the sequences start at H₁
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), Theorem A.8, p.52 (PDF p.54); proof pp.52–54 (PDF pp.54–56)

import Mathlib
import Definitions.Def_ValiantModel_Learnable
import Definitions.Def_ValiantModel_IsCompressionRate

namespace ValiantModel.Supplement

open ValiantModel

/-- **Theorem A.8 (Learnability Is Closed under Unions)**, Hanneke, Mehrotra, Velegkas, Zampetakis,
arXiv:2605.13840 (version held, sha256 f793f255…), p.52 (PDF p.54), in Valiant's model (Definition 1):
if `H` and `G` are learnable, so is `H ∪ G = (H₁ ∪ G₁, H₂ ∪ G₂, …)`. More precisely, if every
realizable `S ⊆ {0,1}^d` has query compression schemes of size `q_H(d)` for `H_d` and `q_G(d)` for
`G_d`, one learner for `H ∪ G` uses, for every `d, ε, δ`, at most
`C (d (q_H(d) + q_G(d)) + log(1/δ)) / ε` examples and `q_H(d) + q_G(d)` membership queries.

**Formalization Note.** `O(·)` is one absolute constant `C`, quantified before the classes and the
size functions. "`H_d` admits query compression schemes of size `q_H(d)`" is
`IsCompressionRate (H d) (fun _ => q_H d)` (Definition 15 with a constant rate). The quantitative
sentence does not assume learnability (its proof does not use it). The learner is the base
mission's `Learner` (a `PMF` over protocols on input `(d, ε, δ)`); its example and query counts are
bounded separately on every protocol in its support. Logarithms are base two. -/
theorem theorem_A_8 :
    (∀ H G : ConceptSequence, Learnable H → Learnable G → Learnable (fun d => H d ∪ G d)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (H G : ConceptSequence) (qH qG : ℕ → ℕ),
      (∀ d : ℕ, 1 ≤ d → IsCompressionRate (H d) (fun _ => qH d)) →
      (∀ d : ℕ, 1 ≤ d → IsCompressionRate (G d) (fun _ => qG d)) →
      ∃ L : Learner, ∀ d : ℕ, 1 ≤ d → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        (∀ p ∈ (L d ε δ).support,
          (p.exampleDepth : ℝ) ≤
              C * ((d : ℝ) * ((qH d + qG d : ℕ) : ℝ) + Real.logb 2 (1 / δ)) / ε ∧
            p.queryDepth ≤ qH d + qG d) ∧
        Guarantee (H d ∪ G d) (L d ε δ) ε δ) := by sorry

end ValiantModel.Supplement
