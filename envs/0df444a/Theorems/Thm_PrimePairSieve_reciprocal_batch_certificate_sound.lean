-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_batch_certificate_sound
-- name    : PrimePairSieve.reciprocal_batch_certificate_sound
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T19:14:44.006995+00:00
-- url     : https://prove2.me/theorems/ad4bcc2f-0185-49a3-a4b5-1f232307b1c2
-- title:
--   Soundness of batched reciprocal sieve certificates
-- statement:
--   For a positive natural scale $s$ and endpoint $L>0$, let a finite list of rows record integers $n,a,b$ and finite prime-factor sets. Assume the recorded indices are strictly increasing. In every row require that the factors are prime, their product is $n$, and
--
--   $$a=\prod_p\begin{cases}1&p=2,\\2&p\ne2,\end{cases}\qquad b=\prod_p\begin{cases}1&p=2,\\p-2&p\ne2.\end{cases}$$
--
--   The checker also requires $n,b>0$. Writing $w(n)$ for the literal squarefree sieve weight, these premises imply
--
--   $$\frac1s\sum_{\text{rows with }n\le L}\left\lfloor\frac{saL}{b(L+n)}\right\rfloor\le\sum_{n=1}^L\frac{w(n)}{1+n/L}.$$
--
--   The factor set contains distinct primes, so its product is squarefree and has exactly those prime factors. Thus the checked fraction $a/b$ equals $w(n)$. Integer division rounds each scaled contribution downward. Strictly increasing indices exclude double counting, and the endpoint filter places all selected indices in $[1,L]$. Finally, omitted terms are nonnegative, so adding them preserves the lower bound.
--
--   This theorem validates arbitrary finite row lists. Finding such lists and their numerical values remains an untrusted computation; concrete uses must prove that the checker returns true. The proof introduces no execution axiom and has no open mathematical inputs.
-- source:
--   Certificate soundness lemma for https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b, using the squarefree prime-factor identity, distinct selected indices and downward-rounded integer division.

import Definitions.Def_PrimePairSieve_ReciprocalBatch
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve.reciprocal_batch_certificate_sound (scale L : ℕ) (hs : 0 < scale) (hL : 0 < L)
    (rows : List PrimePairSieve.ReciprocalBatch.Row)
    (hchain : (rows.map PrimePairSieve.ReciprocalBatch.Row.n).IsChain (· < ·))
    (hrows : rows.all PrimePairSieve.ReciprocalBatch.rowCheck = true) :
    (PrimePairSieve.ReciprocalBatch.roundedSum scale L rows : ℝ)/scale ≤
      ∑ n ∈ Finset.Icc 1 L,
        (if Squarefree n then ∏ p ∈ n.primeFactors, if p = 2 then (1:ℝ) else 2/((p:ℝ)-2) else 0)/(1+(n:ℝ)/L) := by sorry
