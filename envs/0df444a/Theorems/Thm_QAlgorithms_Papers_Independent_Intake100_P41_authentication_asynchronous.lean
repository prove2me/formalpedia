-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P41_authentication_asynchronous
-- name    : QAlgorithms.Papers.Independent.Intake100.P41.authentication_asynchronous
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:19:38.697432+00:00
-- url     : https://prove2.me/theorems/e55ea232-ecd9-4e75-8a6e-ca11eabedc54
-- title:
--   Authentication with retained hash key kept internal in an asynchronous network
-- statement:
--   Let $n\ge1$, let $K$ be finite and nonempty, let $X$ contain at least two messages, and let $T=\{0,1\}^m$, where $m\ge0$. Let $h:K\times X\to T$ be $\varepsilon$-AXU$_2$, with $\varepsilon\ge0$. Authenticate $n$ messages with the same uniform hash key and independent uniform pads, matching the $i$th Alice input and $i$th adversarial submission by their respective arrival orders. The hash key is used internally only for authentication and is destroyed rather than exported after the protocol. There is no timeout: withholding a submitted message produces no Bob response.
--
--   For the real resource $R_n$ and the multiple authentic-channel resource $A_n$ with the fixed independent-tag simulators $\sigma_n$,
--
--   $$
--   d((R_n)_{\rm hon},(A_n)_{\rm hon})=0,\qquad d(R_n,A_n\sigma_n)\le n\varepsilon.
--   $$
--
--   The distance concerns the full interactive resources, including arbitrary joint adaptive attacks and absent outputs. This provides composable authentication without an external synchronization assumption.
-- source:
--   Key recycling in authentication, arXiv:1202.1229v3, PDF p. 16, Corollary 7

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P41

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P41

open QAlgorithms.Papers.Independent.Bridge50.P44 (xorWord verifyTag)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.15--16, Corollary 7: full n epsilon security in a completely
asynchronous network. The key is never exported for arbitrary use; there is
no timeout rejection or synchronization observable. -/
theorem authentication_asynchronous {K X : Type*} [Fintype K] [Nonempty K]
    [Nontrivial X] {m n : ℕ} (hn : 1 ≤ n) (h : K → X → Tag m) (epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) (hh : IsAXU2 h epsilon) :
    PaddedConstructionSecure (n := n) h false ((n : ℝ) * epsilon) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P41

end
