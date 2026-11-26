-- Prove2me | Theorems.Thm_SecSampling_Supplement_lemma_4
-- name    : SecSampling.Supplement.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:00:49.360323+00:00
-- url     : https://prove2.me/theorems/4f38e264-467d-4472-8c23-c8ee1b06d1d6
-- title:
--   Lemma 4 — the universal sequence $t^*$ uniquely solves Eq. (2) and maximizes Eq. (1)
-- statement:
--   There is a unique admissible sequence $t^*$ whose coordinates lie in $(0,1)$ and satisfy, for every $i\ge1$,
--   $$
--   \log\!\left(\frac1{t_i^*}\right)+\sum_{j=1}^{i-1}\frac{(1/t_i^*)^j-1}{j}=1.
--   $$
--   Simultaneously for every $p\in[0,1)$, this same sequence maximizes $F(p,t)$ from Eq. (1) over all $[0,1]$-valued sequences $t$. In particular, $t^*$ is chosen independently of $p$.
--
--   This is the universal threshold sequence used in Theorem 2.
--
--   **Formalization Note** Coordinate `i` is the source coordinate $i+1$. The maximization domain follows the proof's explicit relaxation of monotonicity; after solving the coordinate problems the paper proves that $t^*$ is increasing.
--
--   Differences from the source:
--   - generalization: maximization over the admissible increasing sequences introduced before Theorem 2 → maximization over every $[0,1]$-valued sequence; reason: the proof explicitly relaxes monotonicity, obtains the same maximizer coordinatewise, and then verifies that $t^*$ is increasing
--   - encoding: one-based Eq. (2) → zero-based coordinate `i` representing source coordinate $i+1$; reason: exact reindexing
-- source:
--   Correa, Cristi, Feuilloley, Oosterwijk & Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, Lemma 4 and Eq. (2), p.12 (PDF p.13), proof p.29 (PDF p.30)

import Definitions.Def_SecSampling_Supplement_ROSp

open Set

namespace SecSampling.Supplement

/-- **Lemma 4** (Correa et al., arXiv:2011.07869v1, p.12, PDF p.13; proof p.29,
PDF p.30). There is a unique sequence `t*` whose coordinates in `(0,1)` solve Eq. (2). It is
admissible and, simultaneously for every `p ∈ [0,1)`, maximizes Eq. (1).

**Formalization Note.** Coordinate `i` is the paper's `i+1`. Following the proof, maximality is
stated over every `[0,1]`-valued sequence, not merely over monotone admissible sequences: the
paper first relaxes monotonicity, solves the separable problem, and then proves that `t*` is
increasing. Since `t*` is quantified before `p`, its independence of `p` is literal. -/
theorem lemma_4 :
    ∃! tstar : ℕ → ℝ,
      IsAdmissible tstar ∧
      (∀ i : ℕ, tstar i ∈ Ioo (0 : ℝ) 1 ∧ thresholdEquation i (tstar i)) ∧
      ∀ (p : ℝ), p ∈ Ico (0 : ℝ) 1 →
        ∀ t : ℕ → ℝ, (∀ i, t i ∈ Icc (0 : ℝ) 1) → eqOne p t ≤ eqOne p tstar := by sorry

end SecSampling.Supplement
