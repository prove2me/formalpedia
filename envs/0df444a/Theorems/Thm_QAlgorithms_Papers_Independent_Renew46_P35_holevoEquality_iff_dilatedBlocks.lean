-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P35_holevoEquality_iff_dilatedBlocks
-- name    : QAlgorithms.Papers.Independent.Renew46.P35.holevoEquality_iff_dilatedBlocks
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:04:35.404088+00:00
-- url     : https://prove2.me/theorems/ee2cbe61-3be6-43d4-bf51-6493d93bb879
-- title:
--   Example 9: structure of ensembles with equality in Holevo data processing
-- statement:
--   Let $\{p_x,\rho_x\}$ be a normalized finite density ensemble on $H$. Fix one isometry $V:H\to B\otimes C$, independent of $x$, realizing the channel $\phi(Z)=\operatorname{Tr}_C(VZV^*)$. Write $\Omega_{XBC}=\sum_xp_x|x\rangle\langle x|\otimes V\rho_xV^*$. Then $\chi(\{p_x,\rho_x\})=\chi(\{p_x,\phi(\rho_x)\})$ if and only if there are a unitary decomposition $B=\bigoplus_jL_j\otimes R_j$, normalized densities $\tau_{j,x}$ on $L_j$ and $\omega_j$ on $R_j\otimes C$, and probability distributions $q_j$ and $p(x\mid j)$, such that
--
--   $$\Omega_{XBC}=\bigoplus_jq_j\sum_xp(x\mid j)|x\rangle\langle x|\otimes\tau_{j,x}\otimes\omega_j,\qquad\sum_jq_jp(x\mid j)=p_x.$$
--
--   The equality is understood through the unitary on the retained output $B$. All blocks are nonzero, $\omega_j$ is independent of $x$, and zero-mass conditionals can be arbitrary normalized states. This is the structural equality criterion for a fixed common dilation.
-- source:
--   Structure of states which satisfy strong subadditivity of quantum entropy with equality, arXiv:quant-ph/0304007v2, PDF p. 6, Example 9: structure of ensembles with equality in Holevo data processing

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

/-- PDF p.6, Example 9: equality structure in a fixed common channel dilation.
The isometry is the common unitary with its fixed pure ancillary input inserted. -/
theorem holevoEquality_iff_dilatedBlocks {X H B C : Type}
    [Fintype X] [Fintype H] [Fintype B] [Fintype C]
    [Nonempty X] [Nonempty H] [Nonempty B] [Nonempty C]
    (e : CQData X H) (he : e.Valid) (v : Matrix (B × C) H ℂ) (hv : vᴴ * v = 1)
    (f : Superop H B) (hf : IsChannel f)
    (hdilation : ∀ x, f x = traceRight (v * x * vᴴ)) :
    ensembleInformation e = chiAfter e f ↔
      ∃ d : MarkovTensorBlocks B, ∃ q : Fin d.count → ℝ, ∃ p : Fin d.count → X → ℝ,
      ∃ tau : (j : Fin d.count) → X → Matrix (Fin (d.left j)) (Fin (d.left j)) ℂ,
      ∃ omega : (j : Fin d.count) →
        Matrix (Fin (d.right j) × C) (Fin (d.right j) × C) ℂ,
        (∀ j, 0 ≤ q j) ∧ (∑ j, q j) = 1 ∧
        (∀ j, (∀ x, 0 ≤ p j x) ∧ (∑ x, p j x) = 1) ∧
        (∀ j x, IsDensityMatrix (tau j x)) ∧ (∀ j, IsDensityMatrix (omega j)) ∧
        (∀ x, ∑ j, q j * p j x = e.prob x) ∧
        idTensorSuperop (R := X) (fun x : Matrix H H ℂ =>
          ((v * x : Matrix (B × C) H ℂ) * vᴴ : Matrix (B × C) (B × C) ℂ)) (cqState e.prob e.state) =
          blockState d q (fun j => fun a b => if a.1 = b.1 then
            (p j a.1 : ℂ) * tau j a.1 a.2 b.2 else 0) omega := by sorry

end QAlgorithms.Papers.Independent.Renew46.P35

end
