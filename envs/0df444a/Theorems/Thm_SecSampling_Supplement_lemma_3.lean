-- Prove2me | Theorems.Thm_SecSampling_Supplement_lemma_3
-- name    : SecSampling.Supplement.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:59:59.239526+00:00
-- url     : https://prove2.me/theorems/720027c0-41fa-54f9-966c-f8b66df739e7
-- title:
--   Lemma 3 — the ROSp success guarantee of $ALG_t$ is Eq. (1)
-- statement:
--   Fix $p\in[0,1)$ and an admissible threshold sequence $t$. The ROSp success guarantee of $ALG_t$ equals
--   $$
--   F(p,t)=\sum_{i=1}^{\infty}p^{i-1}\left(1-\max\{p,t_i\}-\int_{\max\{p,t_i\}}^1\sum_{j=1}^i\frac{x-\max\{p,t_i\}}{x^j}\,dx\right).
--   $$
--
--   In particular, $F(p,t)$ lower-bounds every finite-size success probability and finite sizes approach it arbitrarily closely.
--
--   **Formalization Note** The last sentence is the epsilon characterization of the infimum over positive sizes; it avoids any default value for a real `sInf`. The arrival-time cube gives the same uniform-order law as the original ROSp model.
--
--   Differences from the source:
--   - encoding: success guarantee as an infimum over sizes → a lower bound for every size plus epsilon-attainment by some size; reason: this is the defining infimum property and prevents a junk real `sInf`
--   - encoding: one-based sequence and series indices → zero-based Lean indices with `t 0=t₁` and summand `i` representing source index `i+1`; reason: exact reindexing
-- source:
--   Correa, Cristi, Feuilloley, Oosterwijk & Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, Lemma 3 and Eq. (1), p.12 (PDF p.13), proof pp.28–29 (PDF pp.29–30)

import Definitions.Def_SecSampling_Supplement_ROSp

open Set

namespace SecSampling.Supplement

/-- **Lemma 3** (Correa et al., arXiv:2011.07869v1, p.12, PDF p.13; proof pp.28–29,
PDF pp.29–30). For every admissible threshold sequence and `p ∈ [0,1)`, the ROSp success
guarantee of `ALG_t` is the infinite series in Eq. (1).

**Formalization Note.** `eqOne` is Eq. (1), zero-indexed so `t 0=t₁`. `IsALGTGuarantee` says
both that Eq. (1) lower-bounds every finite-size probability and that some size comes within every
positive epsilon; this is the real infimum intended by “success guarantee” without using Lean's
default value for `sInf` on a bad set. -/
theorem lemma_3 (t : ℕ → ℝ) (ht : IsAdmissible t) (p : ℝ) (hp : p ∈ Ico (0 : ℝ) 1) :
    IsALGTGuarantee p t (eqOne p t) := by sorry

end SecSampling.Supplement
