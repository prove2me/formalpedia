-- Prove2me | Theorems.Thm_TransvectionMixing_lemma_5_7_quasi_shear_matching_failure
-- name    : TransvectionMixing.lemma_5_7_quasi_shear_matching_failure
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:19:55.809206+00:00
-- url     : https://prove2.me/theorems/463e82e5-ea11-4724-90d3-4aefd5db3608
-- title:
--   Lemma 5.7 — quasi-shear matching failure $\le |R|5^{|S|}e^{-(|S|+1)N/(n(n-1))}$
-- statement:
--   Assume $n\ge 256$ (the standing assumption of §5.3, p.25). Let $S,R\subseteq[n]$ be nonempty disjoint source and target sets, and let $\tau_1,\tau_2,\tau_3$ be independent uniformly random skeletons, each of length $N$. Define $P_i,Q_i$ as in Lemma 5.5. The probability that, for some $i\in R$, $\tau_2$ fails to match all of $P_i$ to distinct rows of $Q_i$ is at most
--   $$
--   |R|\,5^{|S|}\exp\Bigl(-\frac{(|S|+1)N}{n(n-1)}\Bigr).
--   $$
--
--   It bounds the probability that a skeleton segment fails to realize a quasi-shear.
--
--   Differences from the source:
--   - encoding: three independent random skeletons of length N → the uniform law on triples of skeletons; reason: same probabilities
--   - encoding: laws of the walk over uniform skeletons and uniform coefficients → normalized counts (`prob`, `skelLaw`, `entryLaw`, `piS`) over finite types; reason: Lean convention for finite uniform probability; same values
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), Lemma 5.7, eq. (32), p.28

import Mathlib
import Definitions.Def_TransvectionMixing_walkMat
import Definitions.Def_TransvectionMixing_MatchingCond

namespace TransvectionMixing

/-- **Lemma 5.7** (quasi-shear matching failure) (Braverman–Jain–Newman, *Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over
Large Fields*, manuscript sha256 217f833f…, §5.3.3, p.28). Assume `n ≥ 256` (standing in §5.3, p.25). Let `S, R` be nonempty
disjoint source and target sets, and let `τ₁, τ₂, τ₃` be independent uniform random skeletons,
each of length `N`. Define `P_i, Q_i` as in Lemma 5.5. The probability that, for some
`i ∈ R`, `τ₂` fails to match all of `P_i` to distinct rows of `Q_i` is at most
`|R| 5^{|S|} exp(−(|S| + 1)N/(n(n − 1)))` (eq. (32)). -/
theorem lemma_5_7_quasi_shear_matching_failure (n N : ℕ) (hn : 256 ≤ n) (S R : Finset (Fin n))
    (hS : S.Nonempty) (hR : R.Nonempty) (hSR : Disjoint S R) :
    prob (fun τ : Skel n N × Skel n N × Skel n N =>
        ∃ i ∈ R, ¬ MatchesTarget S i τ.1 τ.2.1 τ.2.2)
      ≤ R.card * 5 ^ S.card
        * Real.exp (-(((S.card : ℝ) + 1) * N / ((n : ℝ) * ((n : ℝ) - 1)))) := by sorry

end TransvectionMixing
