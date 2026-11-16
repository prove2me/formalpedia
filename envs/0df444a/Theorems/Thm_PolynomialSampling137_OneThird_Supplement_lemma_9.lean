-- Prove2me | Theorems.Thm_PolynomialSampling137_OneThird_Supplement_lemma_9
-- name    : PolynomialSampling137.OneThird.Supplement.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:48:48.703849+00:00
-- url     : https://prove2.me/theorems/57e6b8e9-d39e-4dcd-9086-744d26149e34
-- title:
--   Lemma 9 — Even-relation collision criterion, including its target-overlap consequence (18)–(19)
-- statement:
--   Let $d\ge0$, $M=2^{d+1}$ and $\kappa_d=M-d-1$. Let $T\subseteq\mathbb F_2^n$ have no nonempty even zero-sum subset of size at most $M$. For every coordinatewise degree-at-most-$d$ map $Q$ on any finite uniform binary seed, and every subprobability $\nu\le P_Q$ supported on $T$, with mass $\eta$ and point masses at most $\theta$,
--   $$\eta^{\kappa_d}\le(M-1)\theta.$$
--   For every probability target $\pi$ supported on $T$,
--   $$\mathcal O_d(\pi)\le\min\{1,((M-1)\max_y\pi(y))^{1/\kappa_d}\}.$$
--   This weighted criterion permits sampler outputs outside $T$ and supplies the common support estimate for the odd-power and shifted-inverse targets.
--
--   Differences from the source:
--   - encoding: finite binary vector spaces and probability laws → Fin-indexed words, finite fiber sums and structural predicates; reason: the representations preserve all source instances, including zero dimensions and zero masses
-- source:
--   Yan Zhong, Exponential Sampling Lower Bounds for Polynomial Sources, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, Lemma 9, printed p. 14-15; PDF p. 16-17

import Definitions.Def_PolynomialSampling137_OneThird_Supplement_FlatSources

noncomputable section

namespace PolynomialSampling137.OneThird.Supplement

theorem lemma_9 {n : ℕ} (d : ℕ) (T : Set (Word n))
    (hT : NoShortEvenRelation T (2 ^ (d + 1))) :
    (∀ (s : ℕ) (Q : Word s → Word n), MapDegreeLE d Q →
      ∀ (ν : Word n → ℝ) (θ : ℝ), IsSubprobability ν →
      (∀ y, ν y ≤ samplerMass Q y) → SupportedOn ν T → (∀ y, ν y ≤ θ) →
      (∑ y, ν y) ^ CollisionExponent d ≤ ((2 : ℝ) ^ (d + 1) - 1) * θ) ∧
    (∀ π : Word n → ℝ, IsLaw π → SupportedOn π T →
      BestOverlap d π ≤ min 1
        ((((2 : ℝ) ^ (d + 1) - 1) * (Finset.univ.sup' Finset.univ_nonempty π)) ^
          (1 / (CollisionExponent d : ℝ)))) := by sorry

end PolynomialSampling137.OneThird.Supplement
