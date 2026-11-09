-- Prove2me | Theorems.Thm_QuadraticProbe717_Insertion_total_vacancy_covariance
-- name    : QuadraticProbe717.Insertion.total_vacancy_covariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:22:10.030112+00:00
-- url     : https://prove2.me/theorems/b9fd97cf-b08d-4ea9-82c6-639f6f86ffa4
-- title:
--   Lemma 4.2 — total vacancy covariance
-- statement:
--   For the Poissonized table of size $n>0$, rate $(1-\varepsilon)n$ and $0<\varepsilon<1$, let $C(r)=\operatorname{Cov}(F_0,F_r)$. Then
--   $$\sum_{r=0}^{n-1}C(r)\le1.$$
--   The sum includes the variance term at residue zero. The numerical constant is exactly one.
--
--   Differences from the source:
--   - encoding: Poisson((1−ε)n) insertions including N≥n → the discrete mixture of algorithm-generated occupied-set laws with Poisson rate ((1−ε)n).toNNReal; reason: 0<ε<1 makes the rate exact; full tables remain full and subsequent costs are 2n
--   - encoding: sum over residues 0,…,n−1 → finite sum over ZMod n; reason: identical index set without choosing representatives
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), Lemma 4.2, p. 8 (PDF p. 8)

import Definitions.Def_QuadraticProbe717_Insertion_laws

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuadraticProbe717.Insertion

theorem total_vacancy_covariance (n : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∑ r : ZMod n, vacancyCovariance n π (poissonRate n ε) r ≤ 1 := by sorry

end QuadraticProbe717.Insertion
