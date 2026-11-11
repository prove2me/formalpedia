-- Prove2me | Theorems.Thm_PolySwap_KMS_lemma_3_7
-- name    : PolySwap.KMS.lemma_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:42:06.87968+00:00
-- url     : https://prove2.me/theorems/60deb11f-ad2a-4c2a-b068-91d510f41025
-- title:
--   Lemma 3.7 — colour sampling: a uniformly random set of $T\ge r^{10}$ disjoint colour sets is nice with probability $\ge0.9$
-- statement:
--   Let $r\ge10^4$, $T\ge r^{10}$ and $d\ge100(r+1)^2T^2$. Then a uniformly random set $\mathcal I\in\binom{[d]}{r+1}^{[T]}$ of $T$ pairwise disjoint colour sets of size $r+1$ in $[d]=\{0,\dots,d\}$ is nice with probability at least $0.9$:
--   $$\#\{\mathcal I\in\tbinom{[d]}{r+1}^{[T]}:\mathcal I\text{ nice}\}\ \ge\ 0.9\cdot\#\tbinom{[d]}{r+1}^{[T]}.$$
--
--   Differences from the source:
--   - encoding: with probability ≥ 0.9 over a uniformly random I ∈ ([d] choose r+1)^[T] → 0.9 · card (disjointColorSets d r T) ≤ niceCount d r T; reason: the uniform probability of a finite set as a ratio of cardinalities
--   - reading: condition (e) of Definition 3.6: 'for every pair of J-bins B, B′' → IsNice quantifies (e) over every pair (ℓ, ℓ′) of nonempty bins, B = B′ included; empty bins are omitted, as the definition says; reason: a pair is an arbitrary pair, as the proof of Lemma 3.7 counts it (p. 34: 'This count allows the two bins to belong to arbitrary color sets, as in the definition'); reading it as two different bins would weaken Lemma 3.7
--   - reading: niceness evaluated in each J's own cyclic path order with a chosen j₀ ∈ J → IsNice with j₀ = min J (base J); reason: Definition 3.6 states the choice of j₀ does not matter
-- source:
--   Dikstein, Oppenheim, Valentiner-Branth, Polynomial Swap Coboundary Expansion with Applications to LTCs and PCPs, STOC 2027 submission (manuscript sha256 b9cb2095…), Lemma 3.7, p. 24 (proof §4, pp. 31–35)

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex
import Definitions.Def_PolySwap_KMS_Dehn
import Definitions.Def_PolySwap_KMS_KMSComplex

namespace PolySwap.KMS

/-- **Lemma 3.7** (colour sampling), p. 24. Let `r ≥ 10⁴`, `T ≥ r¹⁰` and
`d ≥ 100(r + 1)²T²`. Then a uniformly random set `I ∈ ([d] choose r+1)^[T]` of `T` disjoint
colour sets is nice with probability `≥ 0.9`. -/
theorem lemma_3_7 (r T d : ℕ) (hr : 10 ^ 4 ≤ r) (hT : r ^ 10 ≤ T)
    (hd : 100 * (r + 1) ^ 2 * T ^ 2 ≤ d) :
    (0.9 : ℝ) * (disjointColorSets d r T).card ≤ niceCount d r T := by sorry

end PolySwap.KMS
