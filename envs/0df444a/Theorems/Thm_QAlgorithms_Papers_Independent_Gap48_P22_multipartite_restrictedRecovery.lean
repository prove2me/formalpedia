-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P22_multipartite_restrictedRecovery
-- name    : QAlgorithms.Papers.Independent.Gap48.P22.multipartite_restrictedRecovery
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:22:02.656575+00:00
-- url     : https://prove2.me/theorems/d2c54782-a23c-42c7-8972-96424479e357
-- title:
--   Approximate recovery extension for restricted copy tuples
-- statement:
--   Let $n\ge2$, $k\ge1$, and $\varepsilon\ge0$. Let $\rho^{A_1\cdots A_nE}$ be a density operator on finite positive-dimensional systems whose total conditional information in bits is at most $2\varepsilon$. Put $t=\sqrt{8\ln2}\sqrt\varepsilon$. There exists a density operator $\Omega$ on $A_1A_2^{[k]}\cdots A_n^{[k]}$, where only $A_i$ for $i>1$ has $k$ copies, such that
--
--   $$\left\|\operatorname{Tr}_E\rho-\Omega^{A_1A_2^{j_2}\cdots A_n^{j_n}}\right\|_1\le(n-1)(k-1)t\le nk\sqrt{8\ln2}\sqrt\varepsilon$$
--
--   for every tuple $(j_2,\ldots,j_n)\in\{1,\ldots,k\}^{n-1}$ with at most one entry different from $1$. The displayed reduction of $\Omega$ is its actual selected marginal. This retains precisely the restricted family of tuples justified in the appendix; the general simultaneous-extension conclusion is left open by the paper.
-- source:
--   Squashed entanglement, k-extendibility, quantum Markov chains, and recovery maps, arXiv:1410.4184v4, PDF p. 12, Appendix: restricted-tuple recovery

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Gap48.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P12 (squashedEntanglement KExtendible)

open QAlgorithms.Papers.Independent.Claimed50.P33
  (RegisterBasis registerMarginal entropyAt conditionalMultipartiteInformation singleParties
   forgetEnvironment)

open QAlgorithms.Papers.Independent.Renew46.P35 (classicalCMI)

open QAlgorithms.Entanglement (IsSeparableDensity)

/-- Appendix, PDF p.12: restricted tuples only. Source index 1 becomes 0;
A_1 occurs once. Omega in the norm is its computed selected marginal.
The second displayed estimate is retained as well as the sharper first one. -/
theorem multipartite_restrictedRecovery {n : ℕ} (hn : 2 ≤ n)
    {D : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    {E : Type} [Fintype E] [Nonempty E]
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (hrho : IsDensityMatrix rho) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hsmall : conditionalMultipartiteInformation .total rho (singleParties n) ∅ ≤ 2 * epsilon)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ omega : Matrix (ReplicaBasis D k) (ReplicaBasis D k) ℂ,
      IsDensityMatrix omega ∧
      ∀ j : (i : Fin n) → Fin (partyCopyMultiplicity i k),
        (Finset.univ.filter fun i => i.val ≠ 0 ∧ (j i).val ≠ 0).card ≤ 1 →
        traceNorm (forgetEnvironment rho - selectedReplicaMarginal omega j) ≤
          ((n : ℝ)-1) * ((k : ℝ)-1) * Real.sqrt (8 * Real.log 2) * Real.sqrt epsilon ∧
        ((n : ℝ)-1) * ((k : ℝ)-1) * Real.sqrt (8 * Real.log 2) * Real.sqrt epsilon ≤
          (n : ℝ) * (k : ℝ) * Real.sqrt (8 * Real.log 2) * Real.sqrt epsilon := by sorry

end QAlgorithms.Papers.Independent.Gap48.P22

end
