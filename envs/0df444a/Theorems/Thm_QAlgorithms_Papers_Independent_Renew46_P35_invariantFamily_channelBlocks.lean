-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P35_invariantFamily_channelBlocks
-- name    : QAlgorithms.Papers.Independent.Renew46.P35.invariantFamily_channelBlocks
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:06:28.389762+00:00
-- url     : https://prove2.me/theorems/82a9cd84-bf93-4951-982f-144b04a04c45
-- title:
--   Appendix A, Theorem 10 plus property 2′: valid environment-free block structure
-- statement:
--   Let $\{\rho_k\}_{k\in K}$ be a nonempty finite family of density operators on a nonzero finite-dimensional complex space $H$, with faithful average $|K|^{-1}\sum_k\rho_k$. There are a single unitary decomposition $H=\bigoplus_jL_j\otimes R_j$, states $\tau_{j,k}$ and $\omega_j$, and probability vectors $q_{j\mid k}$ such that
--
--   $$\rho_k=\bigoplus_jq_{j\mid k}\tau_{j,k}\otimes\omega_j.$$
--
--   For every CPTP map $T$ fixing every $\rho_k$, there are CPTP maps $T_j$ on $R_j$ satisfying $T_j(\omega_j)=\omega_j$ and
--
--   $$T(\iota_jZ\iota_j^*)=\iota_j(\operatorname{id}_{L_j}\otimes T_j)(Z)\iota_j^*\quad\text{for every block operator }Z.$$
--
--   Here $\iota_j$ is the orthogonal inclusion supplied by the unitary decomposition. This is the environment-free channel property explicitly proved in Appendix A. It imposes no additional formula on coherences between different blocks.
-- source:
--   Structure of states which satisfy strong subadditivity of quantum entropy with equality, arXiv:quant-ph/0304007v2, PDF p. 7, Appendix A, Theorem 10 plus property 2′: valid environment-free block structure

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P35

noncomputable section

open scoped Matrix ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Renew46.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted interfaces, inspected in the pinned library.

open QAlgorithms.Papers.Independent.Dependency50.P07
  (CQData ensembleMean ensembleInformation accessibleInformation)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAB marginalAC)

open QAlgorithms.Papers.Independent.Dependency50.P21 (petz)

open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection)

open QAlgorithms.Papers.Independent.Information100.P22 (quantumMI)

/-- PDF pp.7–8, Theorem 10(1) and property 2-prime: valid environment-free statement.
No assertion is made about off-diagonal block coherences or unused dilation inputs. -/
theorem invariantFamily_channelBlocks {K H : Type*} [Fintype K] [Fintype H]
    [Nonempty K] [Nonempty H] (rho : K → Matrix H H ℂ)
    (hrho : ∀ k, IsDensityMatrix (rho k))
    (hfaithful : (((Fintype.card K : ℂ)⁻¹) • ∑ k, rho k).PosDef) :
    ∃ d : MarkovTensorBlocks H, ∃ q : K → Fin d.count → ℝ,
    ∃ tau : (j : Fin d.count) → K → Matrix (Fin (d.left j)) (Fin (d.left j)) ℂ,
    ∃ omega : (j : Fin d.count) → Matrix (Fin (d.right j)) (Fin (d.right j)) ℂ,
      (∀ k j, 0 ≤ q k j) ∧ (∀ k, (∑ j, q k j) = 1) ∧
      (∀ j k, IsDensityMatrix (tau j k)) ∧ (∀ j, IsDensityMatrix (omega j)) ∧
      (∀ k, rho k = ∑ j, (q k j : ℂ) • embedTensorBlock d j (Matrix.kronecker (tau j k) (omega j))) ∧
      ∀ f : Superop H H, IsChannel f → (∀ k, f (rho k) = rho k) →
        ∃ fj : (j : Fin d.count) → Superop (Fin (d.right j)) (Fin (d.right j)),
          (∀ j, IsChannel (fj j) ∧ fj j (omega j) = omega j) ∧
          ∀ j x, f (embedTensorBlock d j x) = embedTensorBlock d j (idTensorSuperop (fj j) x) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P35

end
