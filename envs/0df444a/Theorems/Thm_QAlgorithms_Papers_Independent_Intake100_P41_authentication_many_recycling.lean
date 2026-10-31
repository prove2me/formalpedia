-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P41_authentication_many_recycling
-- name    : QAlgorithms.Papers.Independent.Intake100.P41.authentication_many_recycling
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:18:54.701283+00:00
-- url     : https://prove2.me/theorems/7df268b5-5ae1-412d-b4e3-9d423ebdf1d6
-- title:
--   Concurrent multi-message authentication with final key recycling
-- statement:
--   Let $n\ge1$, let $K$ be a finite nonempty key set, let $X$ contain at least two messages, and put $T=\{0,1\}^m$ for $m\ge0$. Suppose $h:K\times X\to T$ is $\varepsilon$-AXU$_2$, where $\varepsilon\ge0$. The input key resource supplies one uniform hash key $k$ and $n$ independent uniform pads $p_1,\ldots,p_n\in T$. Alice tags her $i$th input $x_i$ by $h_k(x_i)\oplus p_i$; Bob verifies his $i$th submitted pair with $p_i$. Sends and submissions are ordered separately, and later sends may precede earlier verifications. Bob exports the retained hash key after all $n$ verifications, or at the common final timeout with a rejection for each missing delivery. Alice exports it at that timeout.
--
--   Let $R_n$ be this real system, and let $S_n$ be the matching multiple authentic-channel resource with a fresh uniform key. Use the $n$ fixed one-message simulators, with independent uniform tags. With honest forwarding filters, the real and ideal systems agree exactly; under arbitrary joint adaptive interaction,
--
--   $$
--   d((R_n)_{\rm hon},(S_n)_{\rm hon})=0,\qquad d(R_n,S_n\sigma_n)\le n\varepsilon.
--   $$
--
--   The reserve contains one hash-index key and exactly $n$ pads, corresponding to the source's key consumption $|k_1|+n|k_2|$. This result supports concurrent authentication followed by arbitrary reuse of the retained key, without requiring synchronization between individual messages.
-- source:
--   Key recycling in authentication, arXiv:1202.1229v3, PDF p. 14, Theorem 6

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P41

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P41

open QAlgorithms.Papers.Independent.Bridge50.P44 (xorWord verifyTag)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.13--15, Theorem 6: one hash key and n fresh pads, concurrent sends,
ordered submissions, final synchronized arbitrary recycling, and n epsilon
resource security. Figure 10 and Section 5.1 fix Bob's earlier release, despite
the proof's inconsistent phrase about both releases occurring at timeout. -/
theorem authentication_many_recycling {K X : Type*} [Fintype K] [Nonempty K]
    [Nontrivial X] {m n : ℕ} (hn : 1 ≤ n) (h : K → X → Tag m) (epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) (hh : IsAXU2 h epsilon) :
    PaddedConstructionSecure (n := n) h true ((n : ℝ) * epsilon) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P41

end
