-- Prove2me | Theorems.Thm_ThreshRankBIS_lemma_9_counting
-- name    : ThreshRankBIS.lemma_9_counting
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:57:03.367287+00:00
-- url     : https://prove2.me/theorems/246fb5a6-4e9e-4c26-85d0-9c77a92fb2fb
-- title:
--   Proof of Lemma 9 — the counting estimator $W_0/\bar\tau$ with $s=\lceil64\eta^{-2}\rceil$ copies
-- statement:
--   Let $I_1,\dots,I_M$ ($M\ge1$) be a list of finite sets, $\lambda>0$, $Z$ the weight of the union and $W_0=\sum_jq^{|I_j|}$, so that a trial accepts with probability $p=Z/W_0$. Let $0<\eta\le1$, $s=\lceil64\eta^{-2}\rceil$, and run $s$ independent copies of the sequence of trials. Let $\tau_i$ be the number of proposals of copy $i$ through acceptance and $\bar\tau$ the mean of $\tau_1,\dots,\tau_s$. Then:
--
--   1. each $\tau_i$ is geometric: $\Pr(\tau_i=m+1)=(1-p)^mp$ for $m\ge0$;
--   2. $\tau_i$ has mean $W_0/Z$ and variance at most $(W_0/Z)^2$;
--   3. by Chebyshev's inequality, $|\bar\tau Z/W_0-1|\le\eta/2$ except with probability at most $1/16$;
--   4. whenever $|\bar\tau Z/W_0-1|\le\eta/2$, $W_0/\bar\tau$ is a relative $\eta$-approximation to $Z$:
--   $$
--   e^{-\eta}Z\le W_0/\bar\tau\le e^{\eta}Z .
--   $$
--
--   This is the counting half of the union algorithm; with $\eta=\epsilon/2$ it approximates the covered weight $Z_T$.
--
--   **Formalization Note** The variance is the extended-valued variance, so an infinite variance is not read as $0$.
--
--   Differences from the source:
--   - generalization: a nonempty list of independent sets of G → a nonempty list of arbitrary finite sets; reason: the argument never uses independence; the paper's list is an instance
--   - reading: the proposal count τ through acceptance (of the trials of the preceding paragraph) → the trials are modelled by Bernoulli variables X i r, independent over all (copy i, trial r), each accepting with probability Z/W₀; τ_i is one plus the index of the first accepting trial of copy i; reason: each trial uses fresh randomness, and its acceptance probability Z/W₀ is clause 4 of the preceding paragraph's statement (lemma_9_trial); the counting paragraph uses nothing else about the trials
--   - generalization: the fugacity λ, rational where it is an algorithm input (p.3) → λ a real number with λ > 0; reason: the statement is about the combinatorial weights and probabilities only and holds for every real λ > 0; it specializes to rational λ
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), Proof of Lemma 9, Counting, p.12

import Mathlib
import Definitions.Def_ThreshRankBIS_unionTrial
set_option autoImplicit false
open Finset MeasureTheory ProbabilityTheory

namespace ThreshRankBIS

/-- **Proof of Lemma 9: counting**, p.12. Let `I_1, …, I_M` (`M ≥ 1`) be a list of finite sets,
`λ > 0`, `Z` the union weight and `W_0 = ∑_j q^{|I_j|}`, so a trial accepts with probability
`p = Z/W_0`. Let `0 < η ≤ 1` and `s = ⌈64η^{−2}⌉`, and run `s` independent copies of the trial
sequence (`X i r` = whether trial `r` of copy `i` accepts). The proposal count `τ_i` through
acceptance satisfies:
1. `τ_i` is geometric: `Pr(τ_i = m + 1) = (1 − p)^m p`;
2. its mean is `W_0/Z` and its variance is at most `(W_0/Z)²`;
3. for the mean `τ̄` of the `s` copies, `|τ̄Z/W_0 − 1| ≤ η/2` except with probability at most
   `1/16` (Chebyshev);
4. whenever `|τ̄Z/W_0 − 1| ≤ η/2`, `W_0/τ̄` is a relative `η`-approximation to `Z`.

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), Proof of Lemma 9,
*Counting*, p.12.

**Formalization Note.** The trials are Bernoulli variables `X i r : Ω → Bool`, independent over
all `(i, r)`, each accepting with probability `Z/W_0` (the acceptance probability of a trial,
proved in the preceding paragraph of the paper). `τ_i` is `1 +` the index of the first accepting
trial of copy `i` (`0` on the null event that none accepts). The variance is the extended
`evariance`, so an infinite variance is not read as `0`. -/
theorem lemma_9_counting {α : Type} [DecidableEq α] {M : ℕ} [NeZero M] (I : Fin M → Finset α)
    (lam : ℝ) (hlam : 0 < lam) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin ⌈64 / η ^ 2⌉₊ → ℕ → Ω → Bool) (hXm : ∀ i r, Measurable (X i r))
    (hXind : iIndepFun (fun p : Fin ⌈64 / η ^ 2⌉₊ × ℕ => X p.1 p.2) P)
    (hXlaw : ∀ i r, P {ω | X i r ω = true} =
      ENNReal.ofReal (unionWeight I lam / W0 I lam)) :
    let Z : ℝ := unionWeight I lam
    let W : ℝ := W0 I lam
    let τ : Fin ⌈64 / η ^ 2⌉₊ → Ω → ℕ := fun i ω => by
      classical
      exact if h : ∃ r, X i r ω = true then Nat.find h + 1 else 0
    let τbar : Ω → ℝ := fun ω => (∑ i, (τ i ω : ℝ)) / (⌈64 / η ^ 2⌉₊ : ℝ)
    (∀ i (m : ℕ), P {ω | τ i ω = m + 1} = ENNReal.ofReal ((1 - Z / W) ^ m * (Z / W))) ∧
    (∀ i, ∫ ω, (τ i ω : ℝ) ∂P = W / Z) ∧
    (∀ i, evariance (fun ω => (τ i ω : ℝ)) P ≤ ENNReal.ofReal ((W / Z) ^ 2)) ∧
    P {ω | η / 2 < |τbar ω * Z / W - 1|} ≤ 1 / 16 ∧
    (∀ ω, |τbar ω * Z / W - 1| ≤ η / 2 →
      Real.exp (-η) * Z ≤ W / τbar ω ∧ W / τbar ω ≤ Real.exp η * Z) := by sorry

end ThreshRankBIS
