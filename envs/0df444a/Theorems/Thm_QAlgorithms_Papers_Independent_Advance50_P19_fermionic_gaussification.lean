-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P19_fermionic_gaussification
-- name    : QAlgorithms.Papers.Independent.Advance50.P19.fermionic_gaussification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:04:04.474963+00:00
-- url     : https://prove2.me/theorems/d87a7127-49dd-4bb8-b275-b2754b6b16e5
-- title:
--   Signed-Hadamard fermionic Gaussification
-- statement:
--   Let $\rho$ be a normalized, parity-preserving state on a finite $q$-mode Fock system. For each $N\ge0$, take $s_N=2^N$ independent copies and mix the copy index of each original mode by $H_N=2^{-N/2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}^{\otimes N}$. The copied CAR representation includes the parity strings of all preceding copies. There exist actual unitary implementations $U_N$ of these mixers and a Gaussian fermionic state $\rho_G$ with the same covariance as $\rho$ such that
--
--   $$\widetilde\rho_{N,j}=\widetilde\rho_{N,k}\quad(1\le j,k\le s_N),\qquad\widetilde\rho_{N,1}\longrightarrow\rho_G\quad(N\to\infty).$$
--
--   Here $\widetilde\rho_{N,j}$ is the actual partial trace of $U_N\rho^{\otimes s_N}U_N^\dagger$ onto copy $j$. Convergence is in finite matrix norm, equivalently trace norm. The mixer acts independently on each original mode and is therefore local for every fixed party split.
-- source:
--   Degradability of Fermionic Gaussian Channels, arXiv:1604.01954v2, PDF p. 12, Unnumbered Gaussification limit

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P19

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P19

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.12, unnumbered signed-Hadamard Gaussification limit: every
copy marginal is identical already at finite N, and converges, in finite
matrix norm, to the Gaussian state with the original covariance. The mixers
and the limiting Gaussian state are conclusions, not input hypotheses.
The finite-copy CAR parity strings are explicit in copyMajorana. -/
theorem fermionic_gaussification {n : ℕ} (s : CARSystem n)
    (rho : Matrix (Qubits n) (Qubits n) ℂ) (hrho : IsFermionicState s rho) :
    ∃ sigma : Matrix (Qubits n) (Qubits n) ℂ,
      IsGaussianState s sigma ∧ fermionicCovariance s sigma = fermionicCovariance s rho ∧
      ∃ U : (N : ℕ) → Matrix.unitaryGroup (Fin (2 ^ N) → Qubits n) ℂ,
        (∀ N, IsGaussificationMixer s N (U N)) ∧
        (∀ N, ∀ j k : Fin (2 ^ N),
          mixedCopyMarginal rho N (U N) j = mixedCopyMarginal rho N (U N) k) ∧
        Filter.Tendsto
          (fun N => mixedCopyMarginal rho N (U N) ⟨0, by positivity⟩)
          Filter.atTop (nhds sigma) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P19

end
