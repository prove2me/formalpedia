-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_weakLaw
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.weakLaw
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:26:32.553102+00:00
-- url     : https://prove2.me/theorems/3b33b923-86c5-4c06-b5bc-904be358c55d
-- title:
--   Lemma I.13: For n>0, delta,epsilon>0 and ||sum rho_i/n−rhoTilde||infty≤epsilon, Tr(rho^n PiC(rhoTilde,delta+epsilon sqrt(n)))≥1−1/delta².
-- statement:
--   Let a nonzero finite system have dimension $d$, and choose a fine orthogonal spectral resolution, including zero eigenspaces and a basis inside degeneracies. All states are normalized, $n>0$, and all typicality tolerances are positive. Write $H$ for entropy in bits, $K_V=2\log_2(e)/e$, $K_H(d)=\max\{(\log_2 3)^2,(\log_2 d)^2\}$, and $h=\sum_iH(\rho_i)$. A shadow $B$ is an effect with state mass at least $\eta$. In the variance bounds put $c=K_Vd\alpha\sqrt n$, $t=2N(\rho)e^{-2\mu(\rho)^2\alpha^2}$, where $N$ counts the positive eigenvalues of $\sqrt{\rho(1-\rho)}$ and $\mu$ is their minimum, or zero on empty support. In the constant-typical bound $\eta(u)=-u\log_2u$, including $u=0$. The weak-law factor states may be noncommuting, with target $\widetilde\rho$ and operator-norm tolerance $\epsilon>0$.
--
--   $$
--   \left\|n^{-1}\sum_i\rho_i-\widetilde\rho\right\|_\infty\le\epsilon\Longrightarrow\operatorname{Tr}\bigl((\rho_1\otimes\cdots\otimes\rho_n)\Pi_{C,\widetilde\rho,\delta+\epsilon\sqrt n}^n\bigr)\ge1-\delta^{-2}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 15, Lemma I.13

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

/-- Lemma I.13, PDF p.15: the printed concentration constant is dimension free.
Factor states need not commute with each other or with the target state. -/
theorem weakLaw {d n : ℕ} (target : FineResolution d) (hn : 0 < n)
    (rho : Fin n → Matrix (Fin d) (Fin d) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i))
    (delta epsilon : ℝ) (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hclose : complexOperatorNorm (((1 / (n : ℝ) : ℝ) : ℂ) • (∑ i, rho i) - target.state) ≤ epsilon) :
    effectProb (wordTensor rho) (constantProjector target n (delta + epsilon * Real.sqrt n)) ≥
      1 - 1 / delta^2 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
