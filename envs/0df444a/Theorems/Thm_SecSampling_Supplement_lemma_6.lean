-- Prove2me | Theorems.Thm_SecSampling_Supplement_lemma_6
-- name    : SecSampling.Supplement.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:01:46.951794+00:00
-- url     : https://prove2.me/theorems/2e413833-c85a-47a8-b87f-e6511628d013
-- title:
--   Lemma 6 (corrected: $\ell$ may take the value 0, as in Lemma 5) — optimal fixed-size ROSp probabilities converge to Eq. (1)
-- statement:
--   Fix $p\in[0,1)$. For every choice, at each positive size $n$, of an optimal sequential-$\ell_{p,n}$-max rule, there is a sequence $t_i\in[0,1]$ such that
--   $$
--   \Pr[\operatorname{SeqMax}_{\ell_{p,n}}\text{ wins}]\longrightarrow F(p,t)
--   \qquad(n\to\infty),
--   $$
--   where $F$ is Eq. (1).
--
--   This limit identifies the asymptotic optimum over all ordinal algorithms with a member of the family optimized in Lemma 4.
--
--   **Formalization Note** Lean indexes the positive sizes as $n+1$. The limiting sequence is not assumed monotone, matching the proof and the relaxed maximization domain of Lemma 4.
--
--   Differences from the source:
--   - reading: “for each $n$, choose $\ell_{p,n}$ so that” → every family of optimal choices has the stated limit; reason: all optimal choices have the same success probability, so the universal and arbitrary-choice readings are equivalent
--   - encoding: positive sizes $n\to\infty$ → Lean index $n$ represents source size $n+1$; reason: excludes only the undefined set $[0]$ and preserves the limit
--   - correction: $\ell_{p,n}:[n]\to[n]$ → $\ell_{p,n}$ takes values in $\{0,\dots,n\}$; reason: as in Lemma 5, no rule with $\ell\ge1$ is optimal (p=0, n=3), so with the printed codomain the hypothesis "optimal" could never hold; the proof's limit function $\tilde\ell$ takes the value 0
-- source:
--   Correa, Cristi, Feuilloley, Oosterwijk & Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, Lemma 6, p.13 (PDF p.14), proof pp.32–33 (PDF pp.33–34)

import Definitions.Def_SecSampling_Supplement_ROSp

open Filter Set Topology

namespace SecSampling.Supplement

/-- **Lemma 6** (Correa et al., arXiv:2011.07869v1, p.13, PDF p.14; proof pp.32–33,
PDF pp.33–34). Fix `p ∈ [0,1)`. For every choice of an optimal sequential-`ℓ`-max algorithm at
each positive size, its success probability converges to Eq. (1) for some `[0,1]`-valued sequence
`t`.

**Formalization Note.** Size index `n` represents the source size `n+1`, excluding only the
undefined zero-size set `[0]`. Sequential thresholds take values in `{0,…,n}` (see `SequentialThreshold`). The optimal
family is universally quantified, as “choose
`ℓ_{p,n}` so that” permits any optimal choice. The limiting `t` is not required to be monotone:
the proof constructs it from a limiting threshold function, and Lemma 4 deliberately maximizes
Eq. (1) over all `[0,1]`-valued sequences. -/
theorem lemma_6 (p : ℝ) (hp : p ∈ Ico (0 : ℝ) 1)
    (ℓ : (n : ℕ) → SequentialThreshold (n + 1))
    (hℓopt : ∀ n, IsOptimalSequential p (n + 1) (ℓ n)) :
    ∃ t : ℕ → ℝ, (∀ i, t i ∈ Icc (0 : ℝ) 1) ∧
      Tendsto
        (fun n => rospWinProb p (sequentialMax (ℓ n)) (canonicalValues (n + 1)))
        atTop (nhds (eqOne p t)) := by sorry

end SecSampling.Supplement
