-- Prove2me | Theorems.Thm_ShuffleDecoys_Hierarchy_eq_1
-- name    : ShuffleDecoys.Hierarchy.eq_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:23:25.264875+00:00
-- url     : https://prove2.me/theorems/34b48cdf-b8ea-4d44-9f0a-0680939e6b6e
-- title:
--   §1.1, Eq. (1) — the shuffled release and the output histogram carry the same information: I_P(M; Z) = I_P(M; T)
-- statement:
--   Let $M\sim P$ on $[d]$, let $R$ be any decoy mechanism (any conditional law of the $n-1$ decoys $H$ given $M$, so every class is covered), let $Z$ be the uniformly shuffled release of $(M,H_2,\dots,H_n)$, and let $T=e_M+S$ with $S=\sum_{i=2}^ne_{H_i}$ the decoy histogram. Then, for every $n\ge1$,
--   $$I_P(M;Z)=I_P(M;T),\qquad T=e_M+S,\qquad S\in\{s\in\mathbb Z^d_{\ge0}:\|s\|_1=n-1\}.$$
--   The shuffled sequence and the output histogram are equivalent experiments for inferring the message; this is what lets every later bound work with count vectors.
--
--   Differences from the source:
--   - encoding: random variables $M,H,\sigma$ → their laws (`PMF`), the release law built by `shuffleLaw`; reason: only laws enter mutual information.
--   - encoding: $n-1$ decoys, release positions $1,\dots,n$ → `Fin (n - 1)` and `Fin n` with hypothesis $n\ge1$; reason: excludes only $n=0$, where there is no release.
--   - encoding: $S\in\{s\in\mathbb Z^d_{\ge0}:\|s\|_1=n-1\}$ → `decoyHist h` is coordinatewise $\ge0$ and sums to $n-1$ for every decoy tuple $h$; reason: same set membership, stated for every value $S$ can take.
--   - reading: the sentence "Conditional on $T$, every ordering of the multiset is equally likely and its distribution is independent of $M$" → not stated separately; reason: it is the justification of the displayed identity (1), which is the claim.
-- source:
--   Su, Cheng, Wang, The Information-Theoretic Limits of Hiding Among Decoys in the Shuffle Model, STOC 2027 submission (manuscript sha256 445baceb…), p. 5, §1.1, Eq. (1)

import Mathlib
import Definitions.Def_ShuffleDecoys_Hierarchy_Info
import Definitions.Def_ShuffleDecoys_Hierarchy_Model

open scoped ENNReal

namespace ShuffleDecoys.Hierarchy

/-- §1.1, Eq. (1): for every decoy mechanism (every kernel, so every class), the shuffled release
`Z` and the output histogram `T = e_M + S` carry the same information about `M`, and the decoy
histogram `S` is a nonnegative integer vector of total mass `n − 1`. -/
theorem eq_1 (d n : ℕ) (hn : 1 ≤ n) (P : PMF (Fin d)) (R : DecoyKernel (Fin d) n) :
    mutualInfo (shuffleLaw P R) = mutualInfo (histLaw P R) ∧
      ∀ h : Fin (n - 1) → Fin d,
        (∀ y, 0 ≤ decoyHist h y) ∧ ∑ y, decoyHist h y = (n : ℤ) - 1 := by sorry

end ShuffleDecoys.Hierarchy
