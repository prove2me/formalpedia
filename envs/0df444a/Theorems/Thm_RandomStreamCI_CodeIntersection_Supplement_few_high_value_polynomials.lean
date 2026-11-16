-- Prove2me | Theorems.Thm_RandomStreamCI_CodeIntersection_Supplement_few_high_value_polynomials
-- name    : RandomStreamCI.CodeIntersection.Supplement.few_high_value_polynomials
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:50:16.86947+00:00
-- url     : https://prove2.me/theorems/47967f19-888b-4224-abf7-2a6cf67350f4
-- title:
--   Lemma 25 (used in the proof of Theorem 27) — Few high-value polynomials: count and sum
-- statement:
--   Let $1\le d\le n$ and let $C\subseteq\Sigma^n$ be a finite code whose distinct words agree on at most $d-1$ coordinates. Fix $A\subseteq U=[n]\times\Sigma$ and any normalized Boolean law $X$ on $\{0,1\}^A$ with $H_\infty(X)\ge|A|-D$. Write $k_c=|T_c\cap A|$ and $E_c=\{|X_{T_c\cap A}|\ge k_c/2+s\}$. If $s\ge3\sqrt n$, $D\le s^2/(8d)$, and $\eta=e^{-s^2/(4n)}$, then
--   $$|\{c\in C:\Pr_X(E_c)\ge2\eta\}|<\frac n{d\eta},\qquad\sum_{c\in C}[\Pr_X(E_c)-2\eta]^+\le\frac n{d\eta}.$$
--   The strict count and the full positive-part sum both hold for arbitrary laws satisfying the entropy condition, without a density-restoring partition. This supports the growth estimate used in Theorem 27.
--
--   Differences from the source:
--   - encoding: coordinates, times and symbols as finite labelled sets → Fin indices numbered from zero and finite alphabet types; reason: bijections of labels preserve every source instance
--   - encoding: a Boolean random variable X and its event probabilities → a normalized PMF on exactly A -> Bool, with the published finite min-entropy; reason: every finite law is represented; there is no independence hypothesis or extension of the event domain
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, release papers-1/71.pdf, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Lemma 25, p. 19 (printed = PDF; offset 0)

import Definitions.Def_RandomStreamCI_CodeIntersection_Supplement_Agreement
import Definitions.Def_RandomStreamCI_CodeIntersection_Supplement_Potential

namespace RandomStreamCI.CodeIntersection.Supplement

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Lemma 25, pp. 19--20: strict high-probability count AND positive-part sum,
for arbitrary pairwise-agreement codes and arbitrary normalized Boolean laws. -/
theorem few_high_value_polynomials {n d : ℕ} {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet]
    (hd0 : 1 ≤ d) (hdn : d ≤ n) (C : Finset (Word n Alphabet))
    (hC : PairwiseAgreement C d) (A : Finset (Address n Alphabet)) (X : PMF (A → Bool))
    (D s : ℝ) (hX : (A.card : ℝ) - D ≤ minEntropy (weights X))
    (hs : 3 * Real.sqrt (n : ℝ) ≤ s) (hD : D ≤ s^2 / (8 * (d : ℝ))) :
    ((C.filter (fun c => 2 * surplusEta n s ≤ highValueProbability A X c s)).card : ℝ) <
        (n : ℝ) / ((d : ℝ) * surplusEta n s) ∧
      (∑ c ∈ C, max (highValueProbability A X c s - 2 * surplusEta n s) 0) ≤
        (n : ℝ) / ((d : ℝ) * surplusEta n s) := by sorry

end RandomStreamCI.CodeIntersection.Supplement
