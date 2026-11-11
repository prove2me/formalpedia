-- Prove2me | Theorems.Thm_SubexpPermanent_Main_lemma_A_2
-- name    : SubexpPermanent.Main.lemma_A_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:00:14.871182+00:00
-- url     : https://prove2.me/theorems/28f52bb1-72f8-4260-bc39-87edf22f7901
-- title:
--   Lemma A.2 — $t[b+\log(z+e)]^2\le2t[b+\log t+1]^2+2z$ for $t\ge1$, $b,z\ge0$
-- statement:
--   For real numbers $t\ge1$ and $b,z\ge0$,
--   $$t\,[\,b+\log(z+e)\,]^2\le 2t\,[\,b+\log t+1\,]^2+2z\qquad(36).$$
--   This inequality shows that the dependence of the optimization accuracy $\xi$ on $n$ adds at most a polynomial factor in $n$ to the running time of Theorem 1.2 (with $t=\sqrt\lambda$, $z=\log n$).
--
--   Differences from the source: none.
-- source:
--   Kudria, Luo, Majid, Subexponential Approximation of the Permanent in Deterministic Polynomial Time, arXiv:2609.10516 (held PDF, sha256 e752b6f0…), p. 38, Lemma A.2, eq. (36)

import Mathlib

namespace SubexpPermanent.Main

/-- Lemma A.2, p. 38, eq. (36). -/
theorem lemma_A_2 (t b z : ℝ) (ht : 1 ≤ t) (hb : 0 ≤ b) (hz : 0 ≤ z) :
    t * (b + Real.log (z + Real.exp 1)) ^ 2 ≤ 2 * t * (b + Real.log t + 1) ^ 2 + 2 * z := by sorry

end SubexpPermanent.Main
