-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P97_standard_cloning_lowerBound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P97.standard_cloning_lowerBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:54:32.782778+00:00
-- url     : https://prove2.me/theorems/73d72f55-a062-4b0f-951b-4244b992c606
-- title:
--   Standard mixed-state cloning with a common ancilla
-- statement:
--   All states are positive semidefinite, trace-one matrices, including pure and rank-deficient states. Write $F(\rho,\sigma)$ for squared Uhlmann fidelity, $f=\sqrt{F(\rho_1,\rho_2)}$, and $D(\rho,\sigma)=\sqrt{1-F(\rho,\sigma)}=\sin\Delta(\rho,\sigma)$.
--
--   Let $H=\mathbb C^d$ with $d>1$ and let $\rho_1\ne\rho_2$ be two density operators on $H$. The auxiliary register $E$ is arbitrary finite dimensional, with no dimension bound. For density operators $\Upsilon_j$ on $H_B\otimes E$, where $H_B=H$, fix one unitary $V$ on $H_A\otimes H_B\otimes E$ for both labels. Set $\widetilde\rho_j=\operatorname{Tr}_E[V(\rho_j\otimes\Upsilon_j)V^\dagger]$, $\phi=\sqrt{F(\Upsilon_1,\Upsilon_2)}$, and
--
--   $$R=\frac{D(\widetilde\rho_1,\rho_1\otimes\rho_1)+D(\widetilde\rho_2,\rho_2\otimes\rho_2)}{D(\rho_1\otimes\rho_1,\rho_2\otimes\rho_2)}.$$
--
--   The initial state factors between the input and the whole ancilla; the ancilla may be mixed and correlated across $B$ and $E$. Distinct inputs ensure a positive denominator.
--
--   If both labels use the same normalized ancillary state $\Upsilon_1=\Upsilon_2=\Upsilon$, then
--
--   $$R\ge f-\frac{f^2}{\sqrt{1+f^2}}.$$
--
--   This is the standard-cloning bound for arbitrary mixed input states. The common ancilla need not be pure or factor between blank and environment.
-- source:
--   Lower bound on the relative error of mixed-state cloning and related operations, arXiv:quant-ph/0208159v2, PDF p. 4, §IV, Eq. (22)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P97

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P97

open QAlgorithms.Papers.Independent.Information100.P67
  (squaredFidelity sineDistance receiverChannel)

open QAlgorithms.Papers.Independent.Dependency50.P48 (densityPower)

/-- PDF p.4, §IV, Eq. (22). Standard cloning uses the same normalized
ancilla for both labels; the blank and environment need not be independent. -/
theorem standard_cloning_lowerBound {d : ℕ} (hd : 1 < d)
    {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
    (rho1 rho2 : Matrix (Fin d) (Fin d) ℂ)
    (tau : Matrix (Fin d × E) (Fin d × E) ℂ)
    (V : Matrix.unitaryGroup ((Fin d × Fin d) × E) ℂ)
    (hrho1 : IsDensityMatrix rho1) (hrho2 : IsDensityMatrix rho2)
    (htau : IsDensityMatrix tau) (hdistinct : rho1 ≠ rho2) :
    standardBound (rootFidelity rho1 rho2) ≤ oneToTwoError rho1 rho2 tau tau V := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P97

end
