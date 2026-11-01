-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P97_n_to_l_cloning_lowerBound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P97.n_to_l_cloning_lowerBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:55:17.837149+00:00
-- url     : https://prove2.me/theorems/d41071ad-ac70-466a-aaee-0c11f2f15144
-- title:
--   Relative error of N to L mixed-state cloning
-- statement:
--   All states are positive semidefinite, trace-one matrices, including pure and rank-deficient states. Write $F(\rho,\sigma)$ for squared Uhlmann fidelity, $f=\sqrt{F(\rho_1,\rho_2)}$, and $D(\rho,\sigma)=\sqrt{1-F(\rho,\sigma)}=\sin\Delta(\rho,\sigma)$.
--
--   Let $d>1$, let $\rho_1\ne\rho_2$ be density operators on $H=\mathbb C^d$, and let $N,M\ge1$ be integers, with $L=N+M$. An arbitrary finite-dimensional environment $E$ and normalized ancillas $\Upsilon_j$ on $H^{\otimes M}\otimes E$ are allowed. Fix a common unitary $V$ on $H^{\otimes L}\otimes E$, and set $\widetilde\rho_j=\operatorname{Tr}_E[V(\rho_j^{\otimes N}\otimes\Upsilon_j)V^\dagger]$ and $\phi=\sqrt{F(\Upsilon_1,\Upsilon_2)}$. With
--
--   $$R_{N\to L}=\frac{D(\widetilde\rho_1,\rho_1^{\otimes L})+D(\widetilde\rho_2,\rho_2^{\otimes L})}{D(\rho_1^{\otimes L},\rho_2^{\otimes L})},$$
--
--   both regimes satisfy
--
--   $$\begin{aligned}f^M\le\phi\le1&\quad\Longrightarrow\quad R_{N\to L}\ge f^N\phi-\frac{f^L\sqrt{1-f^{2N}\phi^2}}{\sqrt{1-f^{2L}}},\\0\le\phi\le f^M&\quad\Longrightarrow\quad R_{N\to L}\ge0.\end{aligned}$$
--
--   Furthermore, for every density operator $\sigma$ on $E$, the choice $\Upsilon_j=\rho_j^{\otimes M}\otimes\sigma$ and $V=I$ gives $R_{N\to L}=0$. This extends the bound and the full-information example to multiple original and additional copies.
--
--   **Formalization Note** The ideal $L$-copy matrix is grouped as its first $N$ and last $M$ factors, using exact entrywise tensor powers.
-- source:
--   Lower bound on the relative error of mixed-state cloning and related operations, arXiv:quant-ph/0208159v2, PDF p. 4, §IV, Eq. (23) and following paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P97

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P97

open QAlgorithms.Papers.Independent.Information100.P67
  (squaredFidelity sineDistance receiverChannel)

open QAlgorithms.Papers.Independent.Dependency50.P48 (densityPower)

/-- PDF p.4, §IV, Eq. (23) and the full-information example after it.
There are `N ≥ 1` original copies and `M ≥ 1` additional copies, `L=N+M`.
The example uses identity evolution; arbitrary evolution could spoil the clones. -/
theorem n_to_l_cloning_lowerBound {d N M : ℕ} (hd : 1 < d)
    (hN : 1 ≤ N) (hM : 1 ≤ M)
    {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
    (rho1 rho2 : Matrix (Fin d) (Fin d) ℂ)
    (tau1 tau2 : Matrix ((Fin M → Fin d) × E) ((Fin M → Fin d) × E) ℂ)
    (V : Matrix.unitaryGroup (((Fin N → Fin d) × (Fin M → Fin d)) × E) ℂ)
    (hrho1 : IsDensityMatrix rho1) (hrho2 : IsDensityMatrix rho2)
    (htau1 : IsDensityMatrix tau1) (htau2 : IsDensityMatrix tau2)
    (hdistinct : rho1 ≠ rho2) :
    let f := rootFidelity rho1 rho2
    let phi := rootFidelity tau1 tau2
    (f ^ M ≤ phi ∧ phi ≤ 1 →
      cloningBound N M f phi ≤ copiesError N M rho1 rho2 tau1 tau2 V) ∧
    (0 ≤ phi ∧ phi ≤ f ^ M → 0 ≤ copiesError N M rho1 rho2 tau1 tau2 V) ∧
    (∀ sigma : Matrix E E ℂ, IsDensityMatrix sigma →
      copiesError N M rho1 rho2
        (Matrix.kronecker (densityPower rho1 M) sigma)
        (Matrix.kronecker (densityPower rho2 M) sigma) 1 = 0) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P97

end
