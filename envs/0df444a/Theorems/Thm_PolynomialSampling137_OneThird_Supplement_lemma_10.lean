-- Prove2me | Theorems.Thm_PolynomialSampling137_OneThird_Supplement_lemma_10
-- name    : PolynomialSampling137.OneThird.Supplement.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:49:33.595944+00:00
-- url     : https://prove2.me/theorems/d3d98f13-3807-4b7f-96f3-bf1993d8c0fe
-- title:
--   Lemma 10 — Odd-power blocks: flatness, degree upper bound, absence of even relations, overlap, and exact minimum degree
-- statement:
--   Fix any binary basis of $K=\mathbb F_{2^r}$ (so $r\ge1$), and $d\ge0$. Put $t=2^d$, $\Phi_d(x)=(x,x^3,\ldots,x^{2t-1})$ and $B_{r,d}=\operatorname{Dist}(\Phi_d(X))$ for uniform $X\in K$. This law is flat of entropy $r$ bits, has an exact degree-at-most-$d+1$ sampler from $r$ bits, and its support has no nonempty even zero-sum subset of size at most $2t$. Moreover,
--   $$\mathcal O_d(B_{r,d})\le\min\{1,((2t-1)2^{-r})^{1/(2^{d+1}-d-1)}\}.$$
--   If $r\ge d+1$, its minimum exact sampling degree is $d+1$. The result covers every positive field dimension, not just powers of two, and supplies the multiscale blocks.
--
--   Differences from the source:
--   - encoding: finite binary vector spaces and probability laws → Fin-indexed words, finite fiber sums and structural predicates; reason: the representations preserve all source instances, including zero dimensions and zero masses
--   - generalization: has a sampler of degree at most d+1 → has such a sampler with seed length exactly r; reason: the source's sampler is Φ_d(X) with X uniform in K, i.e. r seed bits; the Lean conclusion implies the source's existential
-- source:
--   Yan Zhong, Exponential Sampling Lower Bounds for Polynomial Sources, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, Lemma 10, printed p. 16; PDF p. 18

import Definitions.Def_PolynomialSampling137_OneThird_Supplement_BinaryFields

noncomputable section

namespace PolynomialSampling137.OneThird.Supplement

theorem lemma_10 (r d : ℕ) (K : BinaryField r) :
    Flat r (OddPowerLaw K d) ∧
    (∃ Q : Word r → Word (r * 2 ^ d), MapDegreeLE (d + 1) Q ∧
      samplerMass Q = OddPowerLaw K d) ∧
    NoShortEvenRelation {y | 0 < OddPowerLaw K d y} (2 * 2 ^ d) ∧
    BestOverlap d (OddPowerLaw K d) ≤ min 1
      ((((2 : ℝ) ^ (d + 1) - 1) * (2 : ℝ) ^ (-(r : ℤ))) ^
        (1 / (CollisionExponent d : ℝ))) ∧
    (d + 1 ≤ r → MinimumDegree (d + 1) (OddPowerLaw K d)) := by sorry

end PolynomialSampling137.OneThird.Supplement
