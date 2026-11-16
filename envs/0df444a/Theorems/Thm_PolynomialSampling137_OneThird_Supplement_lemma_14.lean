-- Prove2me | Theorems.Thm_PolynomialSampling137_OneThird_Supplement_lemma_14
-- name    : PolynomialSampling137.OneThird.Supplement.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:50:34.40048+00:00
-- url     : https://prove2.me/theorems/98d9b781-389a-4a3a-9f78-1e9e604d42c9
-- title:
--   Lemma 14 — Occupancy bound (28) on arbitrary affine restrictions, including the affinely independent case
-- statement:
--   Let $Q:\mathbb F_2^s\to\mathbb F_2^n$ have coordinate degree at most $d$. Let $\nu\le P_Q$ be a subprobability supported on $T$, of mass $\eta$, with every point mass at most $\theta$. For every $a\ge0$, if $T$ has no nonempty even zero-sum subset of size at most $L(a,d)+1$, then
--   $$\eta\le L(a,d)\bigl(2^{-a}+(1-2^{-a})\theta\bigr),\quad L(a,d)=\sum_{j=0}^{\min(a,d)}\binom aj.$$
--   If $T$ is affinely independent, the conclusion holds for every $a$ without the short-relation condition. This occupancy estimate includes zero mass and $a=0$, and bounds sparse targets without conditioning the sampler.
--
--   Differences from the source:
--   - encoding: finite binary vector spaces and probability laws → Fin-indexed words, finite fiber sums and structural predicates; reason: the representations preserve all source instances, including zero dimensions and zero masses
-- source:
--   Yan Zhong, Exponential Sampling Lower Bounds for Polynomial Sources, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, Lemma 14, printed p. 20; PDF p. 22

import Definitions.Def_PolynomialSampling137_OneThird_Supplement_FlatSources

noncomputable section

namespace PolynomialSampling137.OneThird.Supplement

theorem lemma_14 {s n : ℕ} (d : ℕ) (Q : Word s → Word n)
    (hQ : MapDegreeLE d Q) (T : Set (Word n)) (ν : Word n → ℝ) (θ : ℝ)
    (hν : IsSubprobability ν) (hdom : ∀ y, ν y ≤ samplerMass Q y)
    (hsupp : SupportedOn ν T) (hθ : ∀ y, ν y ≤ θ) :
    (∀ a : ℕ, NoShortEvenRelation T (MonomialCount a d + 1) →
      (∑ y, ν y) ≤ (MonomialCount a d : ℝ) *
        ((2 : ℝ) ^ (-(a : ℤ)) + (1 - (2 : ℝ) ^ (-(a : ℤ))) * θ)) ∧
    (AffinelyIndependent T → ∀ a : ℕ,
      (∑ y, ν y) ≤ (MonomialCount a d : ℝ) *
        ((2 : ℝ) ^ (-(a : ℤ)) + (1 - (2 : ℝ) ^ (-(a : ℤ))) * θ)) := by sorry

end PolynomialSampling137.OneThird.Supplement
