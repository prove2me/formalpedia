-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P12_fixedTypeCovering
-- name    : QAlgorithms.Papers.Independent.Frontier30.P12.fixedTypeCovering
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:06:41.91046+00:00
-- url     : https://prove2.me/theorems/52dbdbc6-6170-459b-bc6c-1bfc2a30d381
-- title:
--   Proposition 4: fixed-type operator covering bound
-- statement:
--   Let $\mathcal X$ be finite and nonempty, and let $W_x$ be normalized states on a $d$-dimensional complex space, $d\ge1$. Fix a probability law $P$ that is an empirical type at some positive length. For every $\epsilon,\delta>0$, there is $n_0$, depending on $W,P,\epsilon,\delta$ but not $M$, such that the following holds for every $n\ge n_0$ with nonempty type class $T_P^n$ and every $M\ge1$. Draw $U(1),\ldots,U(M)$ independently and uniformly from $T_P^n$, with replacement. Write $W_{x^n}^n=\bigotimes_iW_{x_i}$, $\sigma_n(P)=|T_P^n|^{-1}\sum_{x^n\in T_P^n}W_{x^n}^n$, and $I(P;W)=H(\sum_xP(x)W_x)-\sum_xP(x)H(W_x)$. Then
--
--   $$\Pr\!\left[\left\|\frac1M\sum_{j=1}^M W_{U(j)}^n-\sigma_n(P)\right\|_1\ge\epsilon\right]\le2d^n\,2^{-M\iota^n\epsilon/(288\ln2)},\qquad\iota=2^{-I(P;W)-\delta}.$$
--
--   The norm is the full Schatten 1 norm, and $\ln2$ is the natural logarithm. The proposition supplies the fixed-composition covering estimate used for secrecy.
-- source:
--   Distillation of secret key and entanglement from quantum states, arXiv:quant-ph/0306078v1, PDF p. 4, Proposition 4

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P12

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op Vec)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- arXiv:quant-ph/0306078v1, PDF p.4, Proposition 4, proof pp.12--13.
All exponentials have base 2, including the outer exponential; ln 2 is natural.
The threshold is chosen before M, and only compatible positive lengths are used. -/
theorem fixedTypeCovering {X H : Type} [Fintype X] [Fintype H]
    [Nonempty X] [Nonempty H] (p : X → ℝ) (W : X → Op H)
    (hp : IsLaw p) (hW : ∀ x, QAlgorithms.IsDensityMatrix (W x))
    (htype : ∃ n, IsTypeLength p n) (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta) :
    ∃ n0 : ℕ, ∀ n ≥ n0, IsTypeLength p n → ∀ m : ℕ, 0 < m →
      typeSampleProb p n m (fun C =>
        eps ≤ QAlgorithms.traceNorm (typeOutputAverage W C - typeMean p W n)) ≤
      2 * (Fintype.card H : ℝ)^n *
        (2 : ℝ) ^ (-((m : ℝ) * ((2 : ℝ)^(-labelInformation p W - delta))^n * eps /
          (288 * Real.log 2))) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P12

end
