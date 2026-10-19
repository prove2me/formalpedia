-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapD05_dqiDistribution_moments
-- name    : QAlgorithms.Papers.RoadmapD05.dqiDistribution_moments
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:22:20.773156+00:00
-- url     : https://prove2.me/theorems/370a33df-d133-47dc-9eb8-b3b2963b9b8d
-- title:
--   Moments of the DQI distribution
-- statement:
--   Let $p$ be prime, $B\in\mathbb F_p^{m\times n}$, and $F_i\subseteq\mathbb F_p$ satisfy $|F_i|=r$ for every $i$, where $0\le r<p$. For $x\in\mathbb F_p^n$, define the signed objective $f(x)=\sum_{i=1}^m(2\mathbf1_{(Bx)_i\in F_i}-1)$. Let $C^\perp=\{c\in\mathbb F_p^m:B^\mathsf Tc=0\}$ and let $d$ be its minimum nonzero Hamming weight, with $d=+\infty$ when $C^\perp=\{0\}$.
--
--   Let $P\in\mathbb R[t]$ have degree $\ell$, satisfy $\sum_xP(f(x))^2=1$, and obey $2\ell+1\le d$. Define $\mathcal P_{\mathrm{DQI}}(x)=P(f(x))^2$ and $\beta_h=[t^h]P(t)^2$. For every nonnegative integer $k$ such that $k+2\ell<d$,
--   $$
--   \mathbb E_{x\sim\mathcal P_{\mathrm{DQI}}}[f(x)^k]
--   =p^n\mathbb E_{J\sim\operatorname{Binom}(m,r/p)}
--    \left[\sum_{h=0}^{2\ell}\beta_h(2J-m)^{k+h}\right].
--   $$
--   Equivalently, the right side is
--   $$
--   p^n\sum_{j=0}^m\binom mj
--    \left(\frac rp\right)^j\left(1-\frac rp\right)^{m-j}
--    \sum_{h=0}^{2\ell}\beta_h(2j-m)^{k+h}.
--   $$
--
--   This identity characterizes the low-order moments of the signed score under the DQI distribution through binomial moments.
--
--   **Formalization Note** Expectations are finite real sums. The code and its extended natural minimum distance are computed from $B$ using the frozen field-code definitions. The squared-amplitude weights are the frozen real polynomial weights; for real amplitudes they equal the computational-basis probabilities of the frozen DQI state. No additional normalization denominator is introduced.
-- source:
--   Approximate sampling from decoded quantum interferometry via Markov chain Monte Carlo methods, arXiv:2607.28120v1, Theorem 3, Appendix B, Eq. (B60), PDF p. 19. https://arxiv.org/abs/2607.28120v1 . PDF SHA-256: 68009ba5f7fd5f3e426288d3bfe6bb31dbca95c2ce4685ef147a1d2c4daf251a.

import Definitions.Def_QAlgorithms_Defs_PrimeFieldDQIMoments
set_option autoImplicit false

noncomputable section

namespace QAlgorithms.Papers.RoadmapD05

/-- Theorem 3 (Moments of the DQI distribution), arXiv:2607.28120v1,
PDF/printed page 19, Appendix B, Eq. (B60); proof on page 20, Eqs. (B61)--(B62).
The standing assumptions are from pages 2--3 and 13: a prime field, equally sized
satisfaction sets with `r < p`, a real polynomial of degree `ell`, and normalized
amplitudes `P(f(x))`. The signed objective is the frozen `linsatObjective`.
The coefficients on the right are those of the computed square `P ^ 2`.
The distance is computed from the code `ker B.transpose`; its value is infinity
for the zero-only code, agreeing with the proof's absence-of-nonzero-codewords
criterion. The moment range remains strict, as printed in (B60).
-/
theorem dqiDistribution_moments
    {p m n : ℕ} [Fact p.Prime]
    (B : Matrix (Fin m) (Fin n) (ZMod p))
    (F : Fin m → Finset (ZMod p)) (r ell k : ℕ)
    (hr : r < p) (hF : ∀ i, (F i).card = r)
    (P : Polynomial ℝ) (hdegree : P.natDegree = ell)
    (hnormalized : ∑ x : Fin n → ZMod p,
      (P.eval (linsatObjective B F x : ℝ)) ^ 2 = 1)
    (hdecode : (2 * ell + 1 : ℕ∞) ≤
      FieldCodes.minimumDistance (FieldCodes.dualOfEncoder B))
    (hmoment : (k + 2 * ell : ℕ∞) <
      FieldCodes.minimumDistance (FieldCodes.dualOfEncoder B)) :
    ∑ x : Fin n → ZMod p,
      PrimeFieldDQI.realPolynomialWeights B F P hnormalized x *
        (linsatObjective B F x : ℝ) ^ k =
      (p : ℝ) ^ n * ∑ j ∈ Finset.range (m + 1),
        (Nat.choose m j : ℝ) * ((r : ℝ) / (p : ℝ)) ^ j *
          (1 - (r : ℝ) / (p : ℝ)) ^ (m - j) *
          (∑ h ∈ Finset.range (2 * ell + 1),
            (P ^ 2).coeff h * (2 * (j : ℝ) - (m : ℝ)) ^ (k + h)) := by sorry

end QAlgorithms.Papers.RoadmapD05
