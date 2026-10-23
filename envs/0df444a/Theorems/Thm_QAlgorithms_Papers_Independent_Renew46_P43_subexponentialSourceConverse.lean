-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_subexponentialSourceConverse
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.subexponentialSourceConverse
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:30:49.854763+00:00
-- url     : https://prove2.me/theorems/de661b54-50fb-42ff-bf41-15769b7dad60
-- title:
--   Corollary I.20: If En=o(n) and lambda_n≤1−e^(−En), any sequence of arbitrary-encoding (n,lambda_n)Fbar codes has liminf rate≥H(averageState).
-- statement:
--   Let a finite pure-state iid source have average $\bar\rho$. For every positive length $n$, take an arbitrary-encoding code with fidelity error at most $\lambda_n$ and rate $R_n=\log_2\dim\mathcal K_n/n$. Let $(E_n)$ satisfy $E_n/n\to0$.
--
--   $$
--   E_n=o(n),\quad\lambda_n\le1-e^{-E_n}\quad\Longrightarrow\quad\liminf_{n\to\infty}R_n\ge H(\bar\rho).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 20, Corollary I.20

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

/-- Corollary I.20, PDF p.20. The error slack uses e^{-E_n}, and E_n=o(n).
All codes have positive lengths; the ENNReal liminf retains arbitrarily large rates. -/
theorem subexponentialSourceConverse {a d : ℕ} (S : PureSource a d)
    (E lambda : ℕ → ℝ) (hsublinear : Tendsto (fun n : ℕ => E n / (n+1 : ℝ)) atTop (nhds 0))
    (c : ∀ n, SourceCode S (n+1))
    (hcode : ∀ n, 1 - (c n).fidelity ≤ lambda n)
    (herror : ∀ n, lambda n ≤ 1 - Real.exp (-E n)) :
    Filter.liminf (fun n => ENNReal.ofReal (c n).rate) atTop ≥
      ENNReal.ofReal (vnEntropy S.average) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
