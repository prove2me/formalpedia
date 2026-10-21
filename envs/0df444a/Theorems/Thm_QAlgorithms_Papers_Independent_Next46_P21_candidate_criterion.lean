-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P21_candidate_criterion
-- name    : QAlgorithms.Papers.Independent.Next46.P21.candidate_criterion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:39:06.855994+00:00
-- url     : https://prove2.me/theorems/b55cdc13-4d1b-4232-a190-3ffe10731f8f
-- title:
--   Arithmetic and geometric candidate criterion
-- statement:
--   Let $\varepsilon>0$, $\theta\in\mathbb R$, and $k\ge1$ be a natural integer. Let $\alpha=a+b\sqrt2$ and $\beta=c+d\sqrt2$ belong to $\mathbb Z[\sqrt2]$, and set $u=\alpha+i\beta$, $\hat u=u/\sqrt{2^k}$. A candidate means that $\hat u\in\mathcal R_\varepsilon$ and the defect $\xi=x+y\sqrt2=2^k-\overline u u$ has odd $x$, even $y$ and nonnegative values in both real embeddings. Then
--
--   $$
--   \hat u\text{ is a candidate}\quad\Longleftrightarrow\quad\hat u\in\mathcal R_\varepsilon,\ \hat u^\bullet\in D,\ \text{and }a+c\text{ is odd}.
--   $$
--
--   Here $D$ is the closed complex unit disk, $\mathcal R_\varepsilon=\{w\in D:\operatorname{Re}(\overline w e^{-i\theta/2})\ge1-\varepsilon^2/2\}$, and $\bullet$ fixes $i$ and sends $\sqrt2$ to $-\sqrt2$. On the normalized denominator this introduces $(-1)^k$, which is retained. The defect is $\xi=2^k-\alpha^2-\beta^2$, whose $\sqrt2$ coefficient is $-2(ab+cd)$. This equivalence applies to the restricted subring $\mathbb Z[\sqrt2,i]$ and does not require a prime norm.
-- source:
--   Efficient Clifford+T approximation of single-qubit operators, arXiv:1212.6253v2, PDF p. 9, Lemma 21: candidate criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P21

open Set

open scoped ComplexConjugate

/-- Lemma 21, PDF pp.9-10: candidate equivalence on the restricted subring Z[sqrt(2),i].
Equation (28), not its following prose typo, fixes the sign in candidateDefect. -/
theorem candidate_criterion (eps theta : ℝ) (k : ℕ) (alpha beta : Zsqrtd 2)
    (heps : 0 < eps) (hk : 1 ≤ k) :
    IsCandidate eps theta k (quadraticComplex alpha beta) ↔
      (quadraticComplex alpha beta / (Real.sqrt ((2 : ℝ) ^ k) : ℂ)) ∈ epsilonRegion eps theta ∧
      normalizedBullet k alpha beta ∈ unitDisk ∧ Odd (alpha.re + beta.re) := by sorry

end QAlgorithms.Papers.Independent.Next46.P21

end
