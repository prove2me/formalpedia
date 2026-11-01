-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P70_switchedMaximum
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P70.switchedMaximum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:41:31.673068+00:00
-- url     : https://prove2.me/theorems/eb418e38-2919-40fe-947c-d07f51278936
-- title:
--   The maximum coherent information of a retained switched channel
-- statement:
--   Let $S,A,B$ be finite nonempty registers with fixed orthonormal computational bases, and let $\mathcal N_i:A\to B$ be a completely positive trace-preserving map for each basis index $i$ of $S$. Let $\mathcal P_i(X)=|i\rangle\langle i|X|i\rangle\langle i|$ and define the measured, retained switch $\mathcal N=\sum_i\mathcal P_i\otimes\mathcal N_i$. Then
--   $$
--   \max_{\rho^{SA}} I_{\mathrm{coh}}(\mathcal N,\rho^{SA})
--   =\max_i\max_{\rho^A} I_{\mathrm{coh}}(\mathcal N_i,\rho^A).
--   $$
--   All optimizations range over every density matrix on the stated register, and all maxima are attained. In particular there are $i$ and a density matrix $\rho^A$ for which $|i\rangle\langle i|\otimes\rho^A$ attains the left-hand maximum. Coherent information uses entropy in bits.
--
--   Thus correlations and coherent inputs in the switch cannot improve the optimum beyond a definite switch setting.
-- source:
--   Unbounded number of channel uses are required to see quantum capacity, arXiv:1408.5115v1, PDF p. 5, Supplementary Lemma 1, Eq. (S4)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P70

namespace QAlgorithms.Papers.Independent.Intakenext100.P70

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22
  (Op coherentInformation singleUseInformation quantumCapacity mixed)

/-- Supplementary Lemma 1, PDF p.5, S4. Optimization on the left includes all coherent
and correlated switch inputs. The extra attainment clauses express the printed maxima,
rather than assuming maximizing density matrices as hypotheses. -/
theorem switchedMaximum {S A B : Type*} [Fintype S] [Fintype A] [Fintype B]
    [DecidableEq S] [DecidableEq A] [DecidableEq B]
    [Nonempty S] [Nonempty A] [Nonempty B]
    (branches : S → Superop A B) (hbranches : ∀ i, IsChannel (branches i)) :
    singleUseInformation (cubittSwitched branches) =
      sSup (Set.range (fun i => singleUseInformation (branches i))) ∧
    (∀ i, ∃ rho : Op A, IsDensityMatrix rho ∧
      coherentInformation (branches i) rho = singleUseInformation (branches i)) ∧
    ∃ i : S, ∃ rho : Op A, IsDensityMatrix rho ∧
      IsDensityMatrix (cubittSelectedInput i rho) ∧
      coherentInformation (branches i) rho = singleUseInformation (cubittSwitched branches) ∧
      coherentInformation (cubittSwitched branches) (cubittSelectedInput i rho) =
        singleUseInformation (cubittSwitched branches) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P70
