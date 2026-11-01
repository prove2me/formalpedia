-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P97_cloning_relative_lowerBound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P97.cloning_relative_lowerBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:51:42.959437+00:00
-- url     : https://prove2.me/theorems/7d205d80-7820-47e6-a1bd-f9a849b6f0a6
-- title:
--   Relative-error lower bound for two mixed-state clones
-- statement:
--   All states are positive semidefinite, trace-one matrices, including pure and rank-deficient states. Write $F(\rho,\sigma)$ for squared Uhlmann fidelity, $f=\sqrt{F(\rho_1,\rho_2)}$, and $D(\rho,\sigma)=\sqrt{1-F(\rho,\sigma)}=\sin\Delta(\rho,\sigma)$.
--
--   Let $H=\mathbb C^d$ with $d>1$ and let $\rho_1\ne\rho_2$ be two density operators on $H$. The auxiliary register $E$ is arbitrary finite dimensional, with no dimension bound. For density operators $\Upsilon_j$ on $H_B\otimes E$, where $H_B=H$, fix one unitary $V$ on $H_A\otimes H_B\otimes E$ for both labels. Set $\widetilde\rho_j=\operatorname{Tr}_E[V(\rho_j\otimes\Upsilon_j)V^\dagger]$, $\phi=\sqrt{F(\Upsilon_1,\Upsilon_2)}$, and
--
--   $$R=\frac{D(\widetilde\rho_1,\rho_1\otimes\rho_1)+D(\widetilde\rho_2,\rho_2\otimes\rho_2)}{D(\rho_1\otimes\rho_1,\rho_2\otimes\rho_2)}.$$
--
--   The initial state factors between the input and the whole ancilla; the ancilla may be mixed and correlated across $B$ and $E$. Distinct inputs ensure a positive denominator.
--
--   For every such common-unitary device, both of the following bounds hold:
--
--   $$\begin{aligned}f\le\phi\le1&\quad\Longrightarrow\quad R\ge f\phi-\frac{f^2\sqrt{1-f^2\phi^2}}{\sqrt{1-f^4}},\\0\le\phi\le f&\quad\Longrightarrow\quad R\ge0.\end{aligned}$$
--
--   This bounds the relative error using the distinguishability of the input states and of the entire ancillary states.
-- source:
--   Lower bound on the relative error of mixed-state cloning and related operations, arXiv:quant-ph/0208159v2, PDF p. 3, §IV, Theorem (i)–(ii), Eq. (15)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P97

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P97

open QAlgorithms.Papers.Independent.Information100.P67
  (squaredFidelity sineDistance receiverChannel)

open QAlgorithms.Papers.Independent.Dependency50.P48 (densityPower)

/-- PDF pp.3--4, §IV, Theorem (i)--(ii), Eq. (15).
Both regimes are retained, including orthogonal inputs; identical inputs
are excluded because Eq. (14) has no ratio meaning there. -/
theorem cloning_relative_lowerBound {d : ℕ} (hd : 1 < d)
    {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
    (rho1 rho2 : Matrix (Fin d) (Fin d) ℂ)
    (tau1 tau2 : Matrix (Fin d × E) (Fin d × E) ℂ)
    (V : Matrix.unitaryGroup ((Fin d × Fin d) × E) ℂ)
    (hrho1 : IsDensityMatrix rho1) (hrho2 : IsDensityMatrix rho2)
    (htau1 : IsDensityMatrix tau1) (htau2 : IsDensityMatrix tau2)
    (hdistinct : rho1 ≠ rho2) :
    let f := rootFidelity rho1 rho2
    let phi := rootFidelity tau1 tau2
    (f ≤ phi ∧ phi ≤ 1 → cloningBound 1 1 f phi ≤ oneToTwoError rho1 rho2 tau1 tau2 V) ∧
    (0 ≤ phi ∧ phi ≤ f → 0 ≤ oneToTwoError rho1 rho2 tau1 tau2 V) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P97

end
