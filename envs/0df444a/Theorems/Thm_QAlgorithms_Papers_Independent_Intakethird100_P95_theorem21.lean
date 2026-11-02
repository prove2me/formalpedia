-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P95_theorem21
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P95.theorem21
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:37:54.16699+00:00
-- url     : https://prove2.me/theorems/3840b064-66b0-4f3e-a96a-d28010059ab9
-- title:
--   Theorem 21: maximally entangled PPT catalysts, seed headline
-- statement:
--   Let $\lambda=(\lambda_1,\ldots,\lambda_d)$ be a finite probability vector: every entry is nonnegative and the entries sum to one. Write $\rho_\lambda=\sum_{i,j}\sqrt{\lambda_i\lambda_j}|ii\rangle\langle jj|$. All logarithms have base two. A PPT operation is a completely positive, trace-preserving map $L$ such that $\Gamma_{\rm out}L\Gamma_{\rm in}$ is completely positive for arbitrary finite ancillary systems; $\Gamma$ transposes Bob in the fixed product basis. For a positive integer $K$, $\Phi_K$ denotes the maximally entangled state of Schmidt rank $K$. For a finite order $t$, $S_t$ is the Rényi entropy, with $S_0$ the log support size, $S_1=-\sum_i\lambda_i\log_2\lambda_i$ (using $0\log_2 0=0$), and $S_t=(1-t)^{-1}\log_2\sum_i\lambda_i^t$ otherwise. The separate infinity order is $S_\infty=-\log_2\max_i\lambda_i$. Let $K\ge2$ and assume the nonzero spectrum of $\lambda$ is not the uniform spectrum of rank $K$. A maximally entangled catalyst of some finite rank $C\ge2$ exists exactly when
--
--   $$\bigl[\exists C\ge2:\;\Phi_C\otimes\Phi_K\to^{\rm PPT}\Phi_C\otimes\rho_\lambda\bigr]\quad\Longleftrightarrow\quad S_{1/2}(\lambda)<\log_2 K.$$
--
--   The catalyst is returned exactly and uncorrelated with the target, with tensor factors grouped by Alice and Bob. Its rank and the channel may depend on $K$ and $\lambda$. This includes nontrivial targets of rank at most $K$.
--
--   Furthermore, whenever $S_{1/2}(\lambda)<\log_2 K$, there is an integer $C_0\ge2$, depending only on $K$ and $\lambda$, such that for every integer $C\ge C_0$ a PPT channel sends $\Phi_C\otimes\Phi_K$ exactly to $\Phi_C\otimes\rho_\lambda$.
-- source:
--   Pure-state transformations and catalysis under operations that completely preserve positivity of partial transpose, arXiv:0801.4322v2, PDF p. 9, Theorem 21: maximally entangled PPT catalysts, seed headline

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P95

noncomputable section

open scoped BigOperators Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P95

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact primitives from the pinned accepted library; no local aliases.

open QAlgorithms.Papers.Independent.Claimed50.P28 (maximallyEntangledDensity)

open QAlgorithms.Papers.Independent.Information100.P27 (IsProbability)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Information100.P19 (outer)

open QAlgorithms.Papers.Independent.Dependency50.P18 (bipartiteTensor)

open QAlgorithms.Papers.Independent.Support50.P11 (Loewner)

/-- PDF p.9, Theorem 21 (abstract pp.1–2): some finite maximally entangled catalyst
works iff S_{1/2}<log K, excluding the identical nonzero spectrum, up to local unitaries.
The catalyst is returned exactly in tensor product with the target. Below the
threshold, every sufficiently large finite catalyst rank works, as in the proof. -/
theorem theorem21 {d : ℕ} (K : ℕ) (hK : 2 ≤ K) (lam : Fin d → ℝ)
    (hprob : IsProbability lam) (hnontrivial : ¬ IsUniformRank lam K) :
    (CatalyticPreparation K lam ↔ schmidtRenyi (1 / 2) lam < logTwo (K : ℝ)) ∧
    (schmidtRenyi (1 / 2) lam < logTwo (K : ℝ) →
      ∃ C0 : ℕ, 2 ≤ C0 ∧ ∀ C : ℕ, C0 ≤ C →
        Reach (bipartiteTensor (maximallyEntangledDensity C) (maximallyEntangledDensity K))
          (bipartiteTensor (maximallyEntangledDensity C) (schmidtDensity lam))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P95

end
