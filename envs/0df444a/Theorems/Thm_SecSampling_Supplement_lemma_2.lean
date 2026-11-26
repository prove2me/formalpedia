-- Prove2me | Theorems.Thm_SecSampling_Supplement_lemma_2
-- name    : SecSampling.Supplement.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:59:26.703606+00:00
-- url     : https://prove2.me/theorems/d8ce7c91-ae35-55f0-bd5a-66361c64decf
-- title:
--   Lemma 2 — the success probability of $ALG_t$ is non-increasing in the instance size
-- statement:
--   Fix $p\in[0,1)$ and an admissible threshold sequence $0\le t_1<t_2<\cdots<1$. If $P_n(p,t)$ is the ROSp success probability of $ALG_t$ on $n$ distinct values, then for all sizes $m\le n$,
--   $$
--   P_n(p,t)\le P_m(p,t).
--   $$
--
--   Thus the finite-size probabilities decrease weakly toward the success guarantee used in Lemma 3.
--
--   **Formalization Note** The probability is evaluated on a canonical injective value vector; because both the algorithm and the information are ordinal and the online order is uniform, every injective value vector gives the same probability. Sequence index $0$ represents $t_1$.
--
--   Differences from the source:
--   - encoding: arbitrary distinct values and one-based thresholds → the canonical injective values on `Fin n` and `t 0 = t₁`; reason: ordinal invariance under relabelling makes the probabilities identical
-- source:
--   Correa, Cristi, Feuilloley, Oosterwijk & Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, Lemma 2, p.12 (PDF p.13), proof p.27 (PDF p.28)

import Definitions.Def_SecSampling_Supplement_ROSp

open Filter Set

namespace SecSampling.Supplement

/-- **Lemma 2** (Correa, Cristi, Feuilloley, Oosterwijk & Tsigonias-Dimitriadis,
*The Secretary Problem with Independent Sampling*, arXiv:2011.07869v1, p.12, PDF p.13;
proof p.27, PDF p.28). For any admissible threshold sequence and sampling probability in
`[0,1)`, the success probability of `ALG_t` in ROSp is non-increasing with the instance size.

**Formalization Note.** `t 0` is the paper's `t₁`. The probability is evaluated on the canonical
injective values; ordinality and a uniform random order make it independent of the chosen
injective values. “Decreases” is read weakly: whenever `m ≤ n`, the size-`n` probability is
at most the size-`m` probability. -/
theorem lemma_2 (t : ℕ → ℝ) (ht : IsAdmissible t) (p : ℝ) (hp : p ∈ Ico (0 : ℝ) 1) :
    ∀ ⦃m n : ℕ⦄, m ≤ n → algTSizeProb p t n ≤ algTSizeProb p t m := by sorry

end SecSampling.Supplement
