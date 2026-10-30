-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_commuting_optimal_equalities
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.commuting_optimal_equalities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:40:58.475222+00:00
-- url     : https://prove2.me/theorems/5cd7d972-4703-4b02-883f-b734ebba3d8c
-- title:
--   Equation (32): commuting states saturate all optimal bounds
-- statement:
--   Let $d\ge1$, let $\mathcal S$ be the positive semidefinite trace-one matrices on $\mathbb C^d$, including singular matrices, and give $\mathcal S$ its usual matrix topology and Borel sets. Copy counts are positive. A scheme consists of normalized countably additive positive operator measures $E_N$ on $(\mathbb C^d)^{\otimes N}$, fixed independently of the unknown input. Its Born law is $\mu_{N,\rho}(B)=\operatorname{Tr}(\rho^{\otimes N}E_N(B))$. All logarithms are natural.
--
--   Write $I_{\rm Id}$ for the pointwise supremum of all admissible full-estimation rates, $I_{\rm Id}^0$ for the supremum over jointly lower semicontinuous admissible rates, and $I_{\rm Id}^c$ for the supremum over rates admitting a covariant witnessing scheme. These suprema need not themselves be admissible. Let $\widehat I$ denote the principal-minor rate of (26), and write $S(\rho,\sigma)=D(\sigma\Vert\rho)$, with value infinity on support violations.
--
--   If $\rho\sigma=\sigma\rho$, then
--   $$\widehat I(\rho,\sigma)=I_{\rm Id}^c(\rho,\sigma)=I_{\rm Id}^0(\rho,\sigma)=I_{\rm Id}(\rho,\sigma)=D(\sigma\Vert\rho).$$
--   In any common orthonormal eigenbasis, write $\rho=U\operatorname{diag}(r_j)U^*$ and $\sigma=U\operatorname{diag}(t_j)U^*$. The common value is
--   $$\sum_j t_j\bigl(\log t_j-\log r_j\bigr),$$
--   with the support convention. The eigenvalues must be paired in that common basis; sorting them independently is incorrect. This gives exact optimality for commuting states.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 9, Equation (32), corrected final formula

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.9, (32), SOURCE CORRECTION: independently sorted spectra in the last
printed sum are replaced by eigenvalues paired in a common eigenbasis.
For diag(.9,.1),diag(.1,.9), the printed sum is zero whereas the divergence is
.8 log 9. The equality chain itself is retained. -/
theorem commuting_optimal_equalities {d : ℕ} (hd : 0 < d) (rho sigma : DensityOutcome d)
    (hcomm : rho.val * sigma.val = sigma.val * rho.val) :
    fullRate rho sigma = covariantOptimal rho sigma ∧
    covariantOptimal rho sigma = optimalRate FullTarget true rho sigma ∧
    optimalRate FullTarget true rho sigma = optimalRate FullTarget false rho sigma ∧
    optimalRate FullTarget false rho sigma = QuantumLoss.umegakiEntropy sigma.val rho.val sigma.property rho.property ∧
    ∀ (U : Matrix.unitaryGroup (Fin d) ℂ) (r t : Fin d → ℝ),
      rho.val = (U : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal (fun j => (r j : ℂ)) * star (U : Matrix (Fin d) (Fin d) ℂ) →
      sigma.val = (U : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal (fun j => (t j : ℂ)) * star (U : Matrix (Fin d) (Fin d) ℂ) →
      (QuantumLoss.umegakiEntropy sigma.val rho.val sigma.property rho.property : EReal) =
        ((∑ j, t j * Real.log (t j) : ℝ) : EReal) + ∑ j, weightedNegLog (t j) (r j) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
