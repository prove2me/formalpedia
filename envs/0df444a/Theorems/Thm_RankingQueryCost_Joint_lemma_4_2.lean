-- Prove2me | Theorems.Thm_RankingQueryCost_Joint_lemma_4_2
-- name    : RankingQueryCost.Joint.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:25:59.585282+00:00
-- url     : https://prove2.me/theorems/e48a23ee-b754-4bb9-8642-7e9b8c7c696a
-- title:
--   Lemma 4.2 — Random references survive adaptive faults
-- statement:
--   Standing domain: $n\ge16$ is divisible by four, $N=\binom n2$, and the supplied total budget obeys $0\le s\le\lfloor N/32\rfloor$, except for the explicitly generalized band-closure statement. All ranks permute $0,\ldots,n-1$; estimates range over the continuous set $Q$ defined in §2.1.
--
--   Suppose $s<n$ and $256\le k<n$. Choose each reference independently with probability $k/n$, after the preceding history is fixed, and acquire its star. Write $K$ for the number chosen and $\overline H$ for the interval spacing statistic computed from their acquired full scores. Then
--
--   $$\Pr\{k/2\le K\le3k/2\ \text{and}\ \overline H\le2000n^2/k\}\ge15/16.$$
--
--   Later faulty identities and replies may depend on the entire selected set. The formal statement permits any such transcript family whose full stars and disagreement budget hold for one fixed actual order; thus it also applies after every fixed earlier pivot history.
--
--   Differences from the source:
--   - encoding: n labelled objects and unordered distinct comparison identities → Fin n labels and increasing representatives of unordered pairs; reason: this is a bijective representation and leaves the estimate space continuous
--   - encoding: expectation under the stated finite sampling law → the exact finite probability-weighted sum over all masks or independent priority permutations; reason: finite products give precisely the prescribed independent sampling distribution without integrability defaults
--   - generalization: reference selection after a legal pivot history followed by permitted adaptive replies → any transcript family indexed by the reference mask, with full stars and at most s disagreements with a fixed actual order; reason: the proof uses the sampling law and the pointwise score-error bound only; every source experiment induces such a family
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), Lemma 4.2, p. 17, PDF p. 18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Reference

set_option autoImplicit false

namespace RankingQueryCost.Joint

attribute [local instance] Classical.propDecidable

/-- Lemma 4.2, p. 17 / PDF 18. The complete reference set may be used to choose the
subsequent answers: the transcript family is otherwise arbitrary. -/
theorem lemma_4_2 (n s k : ℕ) (hadm : Admissible n s)
    (hs : s < n) (hk : 256 ≤ k ∧ k < n) (r : Rank n)
    (T : (Fin n → Bool) → Transcript n)
    (hT : ∀ mask, r ∈ compatible s (T mask) ∧
      StarsPresent (T mask) (Finset.univ.filter fun i => mask i = true)) :
    (15 / 16 : ℝ) ≤ ∑ mask : Fin n → Bool,
      (∏ i, if mask i then (k : ℝ) / n else 1 - (k : ℝ) / n) *
      (if let S := Finset.univ.filter fun i => mask i = true
          (k : ℝ) / 2 ≤ S.card ∧ (S.card : ℝ) ≤ 3 * k / 2 ∧
            publicSpacing s (T mask) S ≤ 2000 * (n : ℝ) ^ 2 / k
        then 1 else 0) := by sorry

end RankingQueryCost.Joint
