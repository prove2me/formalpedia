-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_varianceTypical
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.varianceTypical
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:22:48.236549+00:00
-- url     : https://prove2.me/theorems/83bdb0c5-40f2-403f-9bf6-46cedfc2733e
-- title:
--   Lemma I.9: PiV has weight≥1−d/alpha² and ≥1−2N e^(−2mu²alpha²); PiV rho^n PiV lies between PiV 2^(−nH±Kd alpha sqrt(n)); rank≤2^(nH+Kd alpha
-- statement:
--   Let a nonzero finite system have dimension $d$, and choose a fine orthogonal spectral resolution, including zero eigenspaces and a basis inside degeneracies. All states are normalized, $n>0$, and all typicality tolerances are positive. Write $H$ for entropy in bits, $K_V=2\log_2(e)/e$, $K_H(d)=\max\{(\log_2 3)^2,(\log_2 d)^2\}$, and $h=\sum_iH(\rho_i)$. A shadow $B$ is an effect with state mass at least $\eta$. In the variance bounds put $c=K_Vd\alpha\sqrt n$, $t=2N(\rho)e^{-2\mu(\rho)^2\alpha^2}$, where $N$ counts the positive eigenvalues of $\sqrt{\rho(1-\rho)}$ and $\mu$ is their minimum, or zero on empty support. In the constant-typical bound $\eta(u)=-u\log_2u$, including $u=0$. The weak-law factor states may be noncommuting, with target $\widetilde\rho$ and operator-norm tolerance $\epsilon>0$.
--
--   $$
--   \operatorname{Tr}(\rho^{\otimes n}\Pi)\ge1-d/\alpha^2,\quad \operatorname{Tr}(\rho^{\otimes n}\Pi)\ge1-t,\quad 2^{-nH(\rho)-c}\Pi\le\Pi\rho^{\otimes n}\Pi\le2^{-nH(\rho)+c}\Pi,\quad\operatorname{Tr}\Pi\le2^{nH(\rho)+c},\quad\operatorname{Tr}B\ge(\eta-t)2^{nH(\rho)-c}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 12, Lemma I.9

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

/-- Lemma I.9, PDF pp.12-13: both concentration estimates, both sandwich sides,
rank bound, and the eta-shadow bound. -/
theorem varianceTypical {d : ℕ} (S : FineResolution d) (n : ℕ) (hn : 0 < n)
    (alpha : ℝ) (halpha : 0 < alpha) :
    let Pi := varianceProjector S n alpha
    let correction := varianceConstant * d * alpha * Real.sqrt n
    effectProb (copies n S.state) Pi ≥ 1 - (d : ℝ) / alpha^2 ∧
    effectProb (copies n S.state) Pi ≥ 1 - varianceTail S alpha ∧
    Below ((exp2 (-n * vnEntropy S.state - correction) : ℂ) • Pi)
      (Pi * copies n S.state * Pi) ∧
    Below (Pi * copies n S.state * Pi)
      ((exp2 (-n * vnEntropy S.state + correction) : ℂ) • Pi) ∧
    Pi.trace.re ≤ exp2 (n * vnEntropy S.state + correction) ∧
    ∀ (B : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) (eta : ℝ),
      IsShadow (copies n S.state) B eta →
      B.trace.re ≥ (eta - varianceTail S alpha) * exp2 (n * vnEntropy S.state - correction) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
