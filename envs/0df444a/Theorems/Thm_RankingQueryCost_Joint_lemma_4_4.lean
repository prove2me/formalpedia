-- Prove2me | Theorems.Thm_RankingQueryCost_Joint_lemma_4_4
-- name    : RankingQueryCost.Joint.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:25:47.259879+00:00
-- url     : https://prove2.me/theorems/53f41d6e-09eb-4104-ba84-2e4259f19cd8
-- title:
--   Lemma 4.4 — Quadratic reference certificate
-- statement:
--   Standing domain: $n\ge16$ is divisible by four, $N=\binom n2$, and the supplied total budget obeys $0\le s\le\lfloor N/32\rfloor$, except for the explicitly generalized band-closure statement. All ranks permute $0,\ldots,n-1$; estimates range over the continuous set $Q$ defined in §2.1.
--
--   Choose a fresh uniform $k$-subset of references, $1\le k\le n$, and acquire its stars after any fixed earlier history. Sort observed reference counts with public-label ties to obtain $\sigma$, and compute $V=16T_2+48n^2s/k$. Then
--
--   $$D_2(r',\sigma)\le V\quad(r'\in\mathcal C_s(T)),\qquad
--   \mathbb EV\le(8n^3+112n^2s)/k.$$
--
--   The compatible-order inequality is pathwise, and the expectation is conditional on the fixed earlier history and actual order. When $k=n$, the alternative public bound is $8u$. Both the primary certificate and this full-table alternative are included. Arbitrary dependence of later replies on the chosen subset is allowed.
--
--   Differences from the source:
--   - encoding: n labelled objects and unordered distinct comparison identities → Fin n labels and increasing representatives of unordered pairs; reason: this is a bijective representation and leaves the estimate space continuous
--   - encoding: expectation under the stated finite sampling law → the exact finite probability-weighted sum over all masks or independent priority permutations; reason: finite products give precisely the prescribed independent sampling distribution without integrability defaults
--   - generalization: the dense-reference construction is used for s at least n, in either support model after legal history → all admissible s and any full-star transcript family compatible with one fixed actual order; reason: the deterministic error and conditional hypergeometric-variance proof only use the pointwise s-disagreement bound; all source histories are covered
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), Lemma 4.4, p. 18, PDF p. 19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Reference

set_option autoImplicit false

namespace RankingQueryCost.Joint

/-- Lemma 4.4, p. 18 / PDF 19. Arbitrary dependence of later answers on the selected
subset is allowed; the actual true order is fixed before the fresh subset. -/
theorem lemma_4_4 (n s k : ℕ) (hadm : Admissible n s) (hk : 1 ≤ k ∧ k ≤ n)
    (r : Rank n) (T : Finset (Fin n) → Transcript n)
    (hT : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      StarsPresent (T S) S ∧ r ∈ compatible s (T S)) :
    (∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      ∀ r' ∈ compatible s (T S),
        squaredError (referenceOrder (T S) S (List.finRange n)) (rankVector r') ≤
          denseCertificate s k (T S) S) ∧
    ((1 / (n.choose k : ℝ)) *
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        denseCertificate s k (T S) S) ≤
      (8 * (n : ℝ) ^ 3 + 112 * (n : ℝ) ^ 2 * s) / k ∧
    (k = n → ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      ∀ r' ∈ compatible s (T S),
        squaredError (referenceOrder (T S) S (List.finRange n)) (rankVector r') ≤
          8 * (crudeScale n s : ℝ)) := by sorry

end RankingQueryCost.Joint
