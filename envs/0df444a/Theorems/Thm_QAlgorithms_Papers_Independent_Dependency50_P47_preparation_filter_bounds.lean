-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P47_preparation_filter_bounds
-- name    : QAlgorithms.Papers.Independent.Dependency50.P47.preparation_filter_bounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:44:44.31598+00:00
-- url     : https://prove2.me/theorems/f9bbdff8-817b-469a-82cb-a74322a6a8ec
-- title:
--   Lemma 4: success probability and error of the preparation filter
-- statement:
--   Fix a finite cq channel $x\mapsto\rho_x$, a law $p(x)$, a block $x^n$, and write $\rho_{x^n}=\bigotimes_i\rho_{x_i}$, $h_F=H(\sum_xp(x)\rho_x)$, and $h_{F|X}=\sum_xp(x)H(\rho_x)$. Let $0<\epsilon<1$ and $\delta,\delta',c>0$, and put $\delta''=\delta'|X|\log_2\dim F+c\delta+|X|c\delta\delta'$. Let $P_x,P$ be orthogonal projectors satisfying
--
--   $$
--   \operatorname{tr}(P_x\rho_{x^n}),\operatorname{tr}(P\rho_{x^n})\ge1-\epsilon,
--   \quad (1-\epsilon)2^{n(h_F-c\delta)}\le\operatorname{tr}P\le2^{n(h_F+c\delta)},
--   \quad P_x\rho_{x^n}P_x\preceq2^{-n(h_{F|X}-\delta'')}P_x.
--   $$
--
--   Let $|\psi\rangle\propto(I\otimes P)|\Phi\rangle$, where $|\Phi\rangle$ is maximally entangled, and set $Q=\sqrt{2^{n(h_{F|X}-\delta'')}}(\sqrt{P_x\rho_{x^n}P_x})^T$. The two operators $Q,\sqrt{I-Q^2}$ form a normalized Kraus measurement. Its success probability $s$ satisfies
--
--   $$
--   s\ge2^{-n(h_F-h_{F|X}+\delta''+c\delta)}(1-4\sqrt\epsilon).
--   $$
--
--   When $s>0$, Bob's normalized branch is the specific double projection $\rho''=\operatorname{normalize}(P\operatorname{normalize}(P_x\rho_{x^n}P_x)P)$, and
--
--   $$
--   \|\rho_{x^n}-\rho''\|_1\le6\epsilon^{1/4}.
--   $$
--
--   This finite-block implication retains the preceding typical-projector facts while avoiding the ambiguous choice of typicality tolerance. Only the poststate assertion is conditional on success.
-- source:
--   On Dimension Bounds for Auxiliary Quantum Systems, arXiv:1207.3911v4, PDF p. 22, Lemma 4: success probability and error of the preparation filter

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P47

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Information100.P48 (normalize)

open QAlgorithms.Papers.Independent.Information100.P62 (IsProjection)

/-- Lemma 4, PDF pp.17,22–23: finite-block implication using exactly the preceding projector
facts. The probability lower bound is unconditional; normalization and error are conditioned only
on a positive-probability success branch. Epsilon is not restricted to make the coarse bound positive. -/
theorem preparation_filter_bounds {x d : ℕ} (hx : 0 < x) (hd : 0 < d)
    (p : Law (Fin x)) (Q : QChannel (Fin x) (Fin d)) (n : ℕ) (xx : Sequence n x)
    (eps delta deltaPrime c : ℝ) (heps0 : 0 < eps) (heps1 : eps < 1)
    (hdelta : 0 < delta) (hdeltaPrime : 0 < deltaPrime) (hc : 0 < c)
    (Pc P : Matrix (Sequence n d) (Sequence n d) ℂ)
    (hPc : IsProjection Pc) (hP : IsProjection P)
    (hacceptC : 1 - eps ≤ effectProb Pc (productDensity Q.rho xx))
    (hacceptP : 1 - eps ≤ effectProb P (productDensity Q.rho xx))
    (hrankLower : (1 - eps) * (2 : ℝ) ^ ((n : ℝ) *
      (vnEntropy (average p.prob Q.rho) - c * delta)) ≤ P.trace.re)
    (hrankUpper : P.trace.re ≤ (2 : ℝ) ^ ((n : ℝ) *
      (vnEntropy (average p.prob Q.rho) + c * delta)))
    (hspectral : (Complex.ofReal ((2 : ℝ) ^ (-((n : ℝ) *
      (averageConditionalEntropy p Q - deltaDouble delta deltaPrime c x d)))) • Pc -
      Pc * productDensity Q.rho xx * Pc).PosSemidef) :
    let rho := productDensity Q.rho xx
    let dd := deltaDouble delta deltaPrime c x d
    let K := preparationFilter n (averageConditionalEntropy p Q) dd rho Pc
    let branch := filterBranch P K
    let success := branch.trace.re
    IsKrausFamily (filterKraus K) ∧
      (2 : ℝ) ^ (-((n : ℝ) * (vnEntropy (average p.prob Q.rho) -
        averageConditionalEntropy p Q + dd + c * delta))) * (1 - 4 * Real.sqrt eps) ≤ success ∧
      (0 < success → branch = (success : ℂ) • doubleProjection rho Pc P ∧
        IsDensityMatrix (doubleProjection rho Pc P) ∧
        traceNorm (rho - doubleProjection rho Pc P) ≤ 6 * eps ^ (1 / 4 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P47

end
