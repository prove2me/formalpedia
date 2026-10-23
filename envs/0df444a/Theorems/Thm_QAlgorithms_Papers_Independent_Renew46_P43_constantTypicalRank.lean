-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_constantTypicalRank
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.constantTypicalRank
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:27:14.968022+00:00
-- url     : https://prove2.me/theorems/3b457e70-b854-477a-b576-4fd4e4a05de4
-- title:
--   Lemma I.14: For 0<delta≤sqrt(n)/(2d), Tr PiC≤(n+1)^d 2^(nH(rho)+nd eta(delta/sqrt(n))), eta(t)=−tlog2 t.
-- statement:
--   Let a nonzero finite system have dimension $d$, and choose a fine orthogonal spectral resolution, including zero eigenspaces and a basis inside degeneracies. All states are normalized, $n>0$, and all typicality tolerances are positive. Write $H$ for entropy in bits, $K_V=2\log_2(e)/e$, $K_H(d)=\max\{(\log_2 3)^2,(\log_2 d)^2\}$, and $h=\sum_iH(\rho_i)$. A shadow $B$ is an effect with state mass at least $\eta$. In the variance bounds put $c=K_Vd\alpha\sqrt n$, $t=2N(\rho)e^{-2\mu(\rho)^2\alpha^2}$, where $N$ counts the positive eigenvalues of $\sqrt{\rho(1-\rho)}$ and $\mu$ is their minimum, or zero on empty support. In the constant-typical bound $\eta(u)=-u\log_2u$, including $u=0$. The weak-law factor states may be noncommuting, with target $\widetilde\rho$ and operator-norm tolerance $\epsilon>0$.
--
--   $$
--   \operatorname{Tr}\Pi_{C,\rho,\delta}^n\le(n+1)^d2^{nH(\rho)+nd\,\eta(\delta/\sqrt n)},\qquad0<\delta\le\sqrt n/(2d).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 15, Lemma I.14

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma I.14, PDF pp.15-16: the correction is n*d*eta(delta/sqrt(n)). -/
theorem constantTypicalRank {d : ℕ} (S : FineResolution d) (n : ℕ) (hn : 0 < n)
    (delta : ℝ) (hdelta : 0 < delta) (hsmall : delta ≤ Real.sqrt n / (2 * d)) :
    (constantProjector S n delta).trace.re ≤ (n + 1 : ℝ)^d *
      exp2 (n * vnEntropy S.state + n * d * etaFunction (delta / Real.sqrt n)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
