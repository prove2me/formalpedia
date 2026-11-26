-- Prove2me | Theorems.Thm_SecSampling_Supplement_lemma_5
-- name    : SecSampling.Supplement.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:01:14.467449+00:00
-- url     : https://prove2.me/theorems/8ce21c2e-09df-5591-843a-e23a09b980dd
-- title:
--   Lemma 5 (corrected: $\ell$ may take the value 0) — a sequential-$\ell$-max algorithm is optimal at each fixed ROSp size
-- statement:
--   Fix $p\in[0,1)$ and a positive instance size $n$. There exists a non-decreasing function $\ell:[n]\to\{0,1,\dots,n\}$ such that the sequential-$\ell$-max algorithm has at least the success probability of every ordinal, possibly randomized algorithm on ROSp instances of size $n$:
--   $$
--   P_n(p,A)\le P_n(p,\operatorname{SeqMax}_\ell)\qquad\text{for every ordinal algorithm }A.
--   $$
--
--   The comparison is among all algorithms in the paper's standing class, not merely among sequential threshold rules.
--
--   **Formalization Note** The sequential rule is a deterministic behavioral algorithm in the published AOSp/ROSp history interface. The positive-size hypothesis only excludes the undefined source set $[0]$. The value $\ell(i)=0$ means that the rule never accepts at observation $i$.
--
--   Differences from the source:
--   - correction: $\ell:[n]\to[n]$, so $\ell\ge1$ → $\ell$ takes values in $\{0,\dots,n\}$; reason: with $\ell\ge1$ the rule accepts the first online element whenever no element is sampled, and the printed lemma is false (at $p=0$, $n=3$ every such rule wins with probability $1/3$, while rejecting the first element and accepting the next running maximum wins with probability $1/2$); the proof's own $\ell(j)=\max\{r:\prod_{s<r}\frac{j-s}{n-s}\ge W(n,j,r)\}$ (p.31) takes the value $0$ (empty product), and Lemma 6's limit uses $\tilde\ell=0$ on $[p,t_1)$
--   - encoding: arbitrary distinct values and the function $\ell$ on $[n]$ → a one-based natural threshold structure with bounds and monotonicity, evaluated on canonical injective values; reason: the same finite map, and ordinal invariance removes the value labels
--   - encoding: possibly randomized ordinal policies → behavioral stopping probabilities on complete relative-rank histories; reason: perfect recall makes behavioral and external randomization equivalent
-- source:
--   Correa, Cristi, Feuilloley, Oosterwijk & Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, Lemma 5, p.12 (PDF p.13), proof pp.30–31 (PDF pp.31–32)

import Definitions.Def_SecSampling_Supplement_ROSp

open Set

namespace SecSampling.Supplement

/-- **Lemma 5** (Correa et al., arXiv:2011.07869v1, p.12, PDF p.13; proof pp.30–31,
PDF pp.31–32). At every fixed positive size and sampling probability `p ∈ [0,1)`, some
non-decreasing sequential-`ℓ`-max algorithm is optimal among all ordinal, possibly randomized
ROSp algorithms.

**Formalization Note.** `SequentialThreshold n` is the paper's
non-decreasing map `ℓ` on the one-based indices `1,…,n`, with values in `{0,…,n}` rather than the
printed `[n]`: the value `0` (never accept at that index) is what the proof's
`ℓ(j) = max{r : …}` produces, and without it the lemma fails (`p = 0`, `n = 3`). Candidate algorithms are the base mission's
behavioural ordinal algorithms and may depend on both `n` and `p`. Uniform random order is the finite
permutation average `rospWinProb`; the canonical injective values lose no information by
ordinality. Positivity of `n` excludes the source's undefined set `[0]`. -/
theorem lemma_5 (p : ℝ) (hp : p ∈ Ico (0 : ℝ) 1) (n : ℕ) (hn : 0 < n) :
    ∃ ℓ : SequentialThreshold n,
      SecSampling.IsAlgorithm (sequentialMax ℓ) ∧ IsOptimalSequential p n ℓ := by sorry

end SecSampling.Supplement
