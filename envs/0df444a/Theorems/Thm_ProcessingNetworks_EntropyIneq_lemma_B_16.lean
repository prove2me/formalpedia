-- Prove2me | Theorems.Thm_ProcessingNetworks_EntropyIneq_lemma_B_16
-- name    : ProcessingNetworks.EntropyIneq.lemma_B_16
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T13:28:06.806049+00:00
-- url     : https://prove2.me/theorems/8ae2b683-4812-4d62-ab09-7f8e97bf2a96
-- title:
--   Lemma B.16 — $(a-d)\log d\le\hat a\log(1\vee\hat d)+1/e$
-- statement:
--   For any real numbers $a,d,\hat a,\hat d$ with $0\le a\le\hat a$ and $0<d\le\hat d$,
--
--   $$
--   (a-d)\log(d)\le\hat a\log(1\vee\hat d)+\frac1e ,
--   $$
--
--   where $1\vee\hat d=\max(1,\hat d)$.
--
--   The bound controls the terms $(d_i-a_i)\log(d_i/\alpha_i)$ of the entropy Lyapunov function uniformly over bounded ranges of $a$ and $d$.
--
--   Differences from the source: none.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix B §B.4, Lemma B.16, eq. (B.35), p.273 (PDF 289)

import Mathlib

namespace ProcessingNetworks.EntropyIneq

/-- **Lemma B.16** (Dai & Harrison, *Processing Networks*, pre-publication draft 2020-4-2,
spnbook.org, Appendix B §B.4, Lemma B.16, eq. (B.35), p.273 (PDF 289)). For any `a, d ∈ ℝ` with
`0 ≤ a ≤ â` and `0 < d ≤ d̂`, the following holds:
`(a − d) log(d) ≤ â log(1 ∨ d̂) + 1/e`.

**Formalization Note** `â`, `d̂` are arbitrary reals (`ahat`, `dhat`) subject only to the stated
inequalities; `1 ∨ d̂ = max 1 d̂` (Guide, p.xv); `e` is `Real.exp 1`; `log` is `Real.log`. -/
theorem lemma_B_16 (a ahat d dhat : ℝ) (ha : 0 ≤ a) (hahat : a ≤ ahat) (hd : 0 < d)
    (hdhat : d ≤ dhat) :
    (a - d) * Real.log d ≤ ahat * Real.log (max 1 dhat) + 1 / Real.exp 1 := by sorry

end ProcessingNetworks.EntropyIneq
