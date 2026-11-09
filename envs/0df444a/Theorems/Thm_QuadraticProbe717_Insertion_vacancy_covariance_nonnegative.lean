-- Prove2me | Theorems.Thm_QuadraticProbe717_Insertion_vacancy_covariance_nonnegative
-- name    : QuadraticProbe717.Insertion.vacancy_covariance_nonnegative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:22:05.003988+00:00
-- url     : https://prove2.me/theorems/4f9e547c-fea8-425b-83be-eff6939e792f
-- title:
--   Observation 3.4 — nonnegative vacancy covariance
-- statement:
--   In the Poissonized table with $n>0$ and $0<\varepsilon<1$, define $C(r)=\operatorname{Cov}(F_0,F_r)$. Then
--   $$\forall r\in\mathbb Z/n\mathbb Z,\quad C(r)\ge0.$$
--   This includes $r=0$ and supplies the sign property as a theorem, never as a hypothesis of the goal.
--
--   Differences from the source:
--   - encoding: Poisson((1−ε)n) insertions including N≥n → the discrete mixture of algorithm-generated occupied-set laws with Poisson rate ((1−ε)n).toNNReal; reason: 0<ε<1 makes the rate exact; full tables remain full and subsequent costs are 2n
--   - encoding: every integer r, with indices modulo n → every element of ZMod n; reason: the covariance is periodic in the integer residue
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), Observation 3.4, p. 7 (PDF p. 7)

import Definitions.Def_QuadraticProbe717_Insertion_laws

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuadraticProbe717.Insertion

theorem vacancy_covariance_nonnegative (n : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (r : ZMod n) :
    0 ≤ vacancyCovariance n π (poissonRate n ε) r := by sorry

end QuadraticProbe717.Insertion
