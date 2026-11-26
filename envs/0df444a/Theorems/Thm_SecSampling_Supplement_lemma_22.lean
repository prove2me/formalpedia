-- Prove2me | Theorems.Thm_SecSampling_Supplement_lemma_22
-- name    : SecSampling.Supplement.lemma_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:02:08.355119+00:00
-- url     : https://prove2.me/theorems/ebf8456a-447f-558e-9ed2-fd813ee13074
-- title:
--   Lemma 22 (corrected: $e^c$ coefficient) — Eq. (1) tends to Samuels' constant
-- statement:
--   There is a unique $c>0$ satisfying
--   $$
--   \int_0^1\frac{e^{cx}-1}{x}\,dx=1.
--   $$
--   For $t'_i=1-c/i$, Eq. (1) has the left limit
--   $$
--   \lim_{p\to1^-}F(p,t')=\gamma
--   =e^{-c}+(e^c-1-c)\int_1^\infty x^{-1}e^{-cx}\,dx,
--   $$
--   Samuels' constant (approximately $0.5801$).
--
--   This supplies the lower-limit computation used in the $p\to1$ clause of Theorem 2.
--
--   **Formalization Note** The formula uses the coefficient derived in the proof on printed p.35. The sequence is zero-indexed, and the limit uses the left-neighborhood filter at $1$.
--
--   Differences from the source:
--   - correction: displayed Eq. (10) has coefficient $e^{-c}-1-c$ → Lean has $e^c-1-c$; reason: the paper's derivation on p.35 itself obtains $e^c-1-c$, while the printed coefficient gives approximately $0.029$ rather than the stated $0.5801$
--   - encoding: $i\ge1$ and $p\to1$ from below → `tPrime c i = 1-c/(i+1)` and the left-neighborhood filter at $1$; reason: exact reindexing and the sampling domain is $p<1$
-- source:
--   Correa, Cristi, Feuilloley, Oosterwijk & Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, Lemma 22 and Eq. (10), p.34 (PDF p.35), corrected by the derivation on p.35 (PDF p.36)

import Definitions.Def_SecSampling_Supplement_ROSp

open Filter Set Topology

namespace SecSampling.Supplement

/-- **Lemma 22 (corrected)** (Correa et al., arXiv:2011.07869v1, p.34, PDF p.35;
derivation p.35, PDF p.36). There is a unique positive `c` satisfying
`∫₀¹ (exp(c x)-1)/x dx = 1`; when Eq. (1) is evaluated at `t'_i=1-c/i`, it tends as `p→1⁻` to
Samuels' constant
`exp(-c) + (exp(c)-1-c) ∫₁^∞ x⁻¹ exp(-c x) dx`.

**Formalization Note.** The displayed Eq. (10) prints the coefficient `exp(-c)-1-c`, but the
paper's derivation on the next page obtains `exp(c)-1-c`; only the latter yields the stated
approximately `0.5801`. The theorem records that evidenced correction. Sequence indices are
shifted by one (`tPrime c 0 = 1-c`). The left-neighbourhood filter is the genuine limit
`p → 1⁻`, not a liminf bound. -/
theorem lemma_22 :
    ∃! c : ℝ, IsSamuelsC c ∧
      Tendsto (fun p : ℝ => eqOne p (tPrime c)) (nhdsWithin 1 (Iio 1))
        (nhds (samuelsGamma c)) := by sorry

end SecSampling.Supplement
