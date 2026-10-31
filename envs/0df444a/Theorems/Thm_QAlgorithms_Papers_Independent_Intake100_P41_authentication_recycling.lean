-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P41_authentication_recycling
-- name    : QAlgorithms.Papers.Independent.Intake100.P41.authentication_recycling
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:17:51.542608+00:00
-- url     : https://prove2.me/theorems/ee6670ff-87bc-4d51-87f3-b5097a9d57cf
-- title:
--   One-message authentication with arbitrary key recycling
-- statement:
--   Let $K$ be a finite nonempty hash-key set, let $X$ contain at least two messages, and let $T=\{0,1\}^m$, where $m\ge0$. Let $\{h_k:X\to T\}_{k\in K}$ be $\varepsilon$-AXU$_2$, with $\varepsilon\ge0$. Alice and Bob share a uniform $k\in K$ and an independent uniform pad $p\in T$. Alice sends $(x,h_k(x)\oplus p)$ over an insecure channel. Bob processes one submitted pair, accepting exactly when its tag verifies, or rejects at timeout if no pair arrived. He releases $k$ upon that verification or timeout; Alice releases it only at timeout. Late submissions are ignored.
--
--   Let $R$ be this real system and let $S$ be the ideal authentic channel with a fresh independent uniform key and the same release schedule. Fix the simulator that generates a uniform tag and permits delivery only of the exact previously sent pair. If $R_{\rm hon},S_{\rm hon}$ denote the resources with their honest forwarding filters, then
--
--   $$
--   d(R_{\rm hon},S_{\rm hon})=0,\qquad d(R,S\sigma)\le\varepsilon.
--   $$
--
--   Here $d$ is unrestricted distinguishing advantage over complete causal interactions at all interfaces. In particular, an impersonation-first environment can read Bob's released key before choosing Alice's message. This construction allows arbitrary subsequent use of the released key with the stated error.
--
--   **Formalization Note** Both distances are expressed through all causal binary tests of explicit execution functions. The simulator is fixed in those functions before the test is chosen.
-- source:
--   Key recycling in authentication, arXiv:1202.1229v3, PDF p. 11, Theorem 5

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P41

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P41

open QAlgorithms.Papers.Independent.Bridge50.P44 (xorWord verifyTag)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.11--13, Theorem 5: honest distance zero and full adversarial
resource distance at most epsilon with the fixed Figure 8 simulator. Nontrivial
X is the proof's implicit convention, including the epsilon >= 1/|T| step. -/
theorem authentication_recycling {K X : Type*} [Fintype K] [Nonempty K]
    [Nontrivial X] {m : ℕ} (h : K → X → Tag m) (epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) (hh : IsAXU2 h epsilon) :
    PaddedConstructionSecure (n := 1) h true epsilon := by sorry

end QAlgorithms.Papers.Independent.Intake100.P41

end
