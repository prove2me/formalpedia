-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P47_remote_preparation_minimum
-- name    : QAlgorithms.Papers.Independent.Dependency50.P47.remote_preparation_minimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:44:04.394842+00:00
-- url     : https://prove2.me/theorems/1cf1a267-4824-485e-a646-309895e28692
-- title:
--   Theorem 5: remote state preparation with classical side information
-- statement:
--   Fix a finite normalized law $p(x,y)$ and a cq channel $x\mapsto\rho_x^F$ with positive finite output dimension. Alice receives $X^n$ and Bob receives $Y^n$; they may share arbitrary finite input-independent entanglement, varying with blocklength. Alice sends a one-way classical message $M$ and Bob prepares $\widetilde F^n$. A rate $R$ is achievable when there are positive slacks $s_n\to0$ such that $\log_2|M|\le n(R+s_n)$ and
--
--   $$
--   \bigl\|\sigma^{X^nY^n\widetilde F^n}-(\rho^{XYF})^{\otimes n}\bigr\|_1\longrightarrow0,
--   \qquad
--   \rho^{XYF}=\sum_{x,y}p(x,y)|x,y\rangle\langle x,y|\otimes\rho_x^F.
--   $$
--
--   The achievable-rate set has an attained least element:
--
--   $$
--   \min\mathcal R_{\mathrm{RSP}}=I(X;F\mid Y).
--   $$
--
--   The error is global and retains the classical references. The communication cost here is logarithmic message cardinality, distinct from the entropy cost used for correlation simulation.
-- source:
--   On Dimension Bounds for Auxiliary Quantum Systems, arXiv:1207.3911v4, PDF p. 21, Theorem 5: remote state preparation with classical side information

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P47

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Information100.P48 (normalize)

open QAlgorithms.Papers.Independent.Information100.P62 (IsProjection)

/-- Theorem 5, PDF pp.20–21: the minimum rate is attained and equals I(X;F|Y).
No preservation of a preassigned purification is asserted. -/
theorem remote_preparation_minimum {x y d : ℕ} (hx : 0 < x) (hy : 0 < y) (hd : 0 < d)
    (p : Law (Fin x × Fin y)) (Q : QChannel (Fin x) (Fin d)) :
    IsLeast (preparationRates p Q) (qCMI p.prob (fun v => Q.rho v.1) Prod.fst Prod.snd) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P47

end
