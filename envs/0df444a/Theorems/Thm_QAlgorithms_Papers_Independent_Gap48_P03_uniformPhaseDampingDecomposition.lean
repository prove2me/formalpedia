-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P03_uniformPhaseDampingDecomposition
-- name    : QAlgorithms.Papers.Independent.Gap48.P03.uniformPhaseDampingDecomposition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:58:38.707994+00:00
-- url     : https://prove2.me/theorems/db1aaa75-43f1-4ac2-9cc1-fc0e00a2dcb0
-- title:
--   Strictly positive finite uniform phase-damping decomposition
-- statement:
--   Let $d\ge2$ and $-1/(d^2-1)\le\lambda\le1$. Write $\Delta_\lambda(X)=\lambda X+(1-\lambda)\operatorname{Tr}(X)I/d$. All states are positive semidefinite with trace one; all information quantities use natural logarithms with $0\log0=0$. For a basis $B=(u_i)$ write $\Phi_{\lambda,B}(X)=\lambda X+(1-\lambda)\sum_i E_iXE_i$, where $E_i=|u_i\rangle\langle u_i|$. A basis is uniform when every one of its vectors has equal coordinate magnitudes in the fixed computational basis. With $N=2d^2(d+1)$, there exist numbers $c_n>0$ summing to one, unitaries $U_n$, and uniform orthonormal bases $B_n$, defining CPTP phase-damping maps, such that simultaneously for all states $\rho$,
--
--   $$\Delta_\lambda(\rho)=\sum_{n=1}^{N}c_nU_n^*\Phi_{\lambda,B_n}(\rho)U_n.$$
--
--   The same decomposition works for every input state and uses precisely the source’s number of terms.
-- source:
--   The capacity of the quantum depolarizing channel, arXiv:quant-ph/0204172v2, PDF p. 10, Lemma 8: finite convex decomposition into uniform phase-damping maps with output unitaries

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P03

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

namespace QAlgorithms.Papers.Independent.Gap48.P03

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage depolarizing)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy holevo IsLaw)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten block)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

open QAlgorithms.Papers.Independent.Claimed50.P43 (ordinaryLimit)

open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- King quant-ph/0204172v2, PDF p.10, Lemma 8, (32).
Exactly the printed number of strictly positive weights, including parameter endpoints.
Conjugation is on the output only. -/
theorem uniformPhaseDampingDecomposition {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (lam : ℝ) (hlow : -1 / ((d : ℝ)^2 - 1) ≤ lam) (hhigh : lam ≤ 1) :
    ∃ (c : Fin (2 * d^2 * (d+1)) → ℝ)
      (U B : Fin (2 * d^2 * (d+1)) → Matrix.unitaryGroup (Fin d) ℂ),
      (∀ n, 0 < c n) ∧ (∑ n, c n) = 1 ∧
      (∀ n, IsUniformBasis (B n : Matrix (Fin d) (Fin d) ℂ) ∧
        IsChannel (phaseChannel (B n : Matrix (Fin d) (Fin d) ℂ) lam)) ∧
      ∀ rho : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix rho →
        depolarizing d (1 - lam) rho = ∑ n, (c n : ℂ) •
          conjSuperop ((U n : Matrix (Fin d) (Fin d) ℂ)ᴴ)
            (phaseChannel (B n : Matrix (Fin d) (Fin d) ℂ) lam rho) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P03

end
