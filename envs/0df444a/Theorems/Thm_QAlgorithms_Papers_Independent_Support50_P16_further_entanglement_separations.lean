-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P16_further_entanglement_separations
-- name    : QAlgorithms.Papers.Independent.Support50.P16.further_entanglement_separations
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:20:00.655015+00:00
-- url     : https://prove2.me/theorems/677094cc-83d3-48dc-b94a-6d78a8c2eeaa
-- title:
--   Unnumbered further strict separations in Section VII
-- statement:
--   For each of the following inequalities there is a normalized bipartite density matrix on some nonzero finite-dimensional local registers that witnesses strictness. Different inequalities may have different states and dimensions:
--
--   $$
--   \begin{gathered}
--   E_c>E_r^\infty,\quad E_{\mathrm{sq},c}^\infty>E_r^\infty,\quad
--   E_r^\infty>E_{r,\to}^\infty,\quad E_r^\infty>K_d,\\
--   E_I>E_{r,\leftrightarrow}^\infty,\quad E_{\mathrm{sq}}>E_{r,\to}^\infty,\quad E_{\mathrm{sq}}>K_d,\\
--   E_I>E_r,\qquad E_{\mathrm{sq}}>E_{r,\leftrightarrow}^\infty.
--   \end{gathered}
--   $$
--
--   There is also an entangled density matrix with $E_d=0<E_{r,\to}^\infty$. Here $E_c,E_d,K_d$ are the operational LOCC formation, distillation, and secret-key rates; $E_r$ is relative entropy of entanglement; $E_{r,\leftrightarrow}$ is its LOCC-measurement version; and $E_{r,\to}$ optimizes the one-way measured version after arbitrary finite-output LOCC operations. The measures $E_{\mathrm{sq}},E_{\mathrm{sq},c},E_I$ are, respectively, half the extension infima of conditional mutual information, its classical-flag restriction, and $I(AA';BB')-I(A';B')$. All regularizations are actual per-copy limits in bits. These directional witnesses do not assert the conjectural converse directions mentioned on p.15.
-- source:
--   Relative entropy and squashed entanglement, arXiv:1210.3181v2, PDF p. 16, Unnumbered further strict separations in Section VII

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P16

namespace QAlgorithms.Papers.Independent.Support50.P16

noncomputable section

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "tau" => QAlgorithms.Papers.Independent.Information100.P76.maximallyMixed

local notation "RE" => QAlgorithms.Papers.Independent.Information100.P54.relativeEntanglement

local notation "RER" => QAlgorithms.Papers.Independent.Information100.P54.regularizedEntanglement

local notation "SQ" => QAlgorithms.Papers.Independent.Dependency50.P19.squashed

local notation "CMI" => QAlgorithms.Papers.Independent.Dependency50.P19.conditionalMutual

local notation "MI" => QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation

local notation "LOCC" => QAlgorithms.Papers.Independent.Information100.P21.FiniteLOCC

local notation "power" => QAlgorithms.Papers.Independent.Dependency50.P42.dimensionedPower

local notation "index" => QAlgorithms.Papers.Independent.Dependency50.P42.copyIndex

-- Accepted matrix coordinates (not P50.Bipartite, which is a vector space).

local notation "Bipartite" => QAlgorithms.Papers.Independent.Dependency50.P50.BipartiteMat

-- Positive outcome counts follow already from a POVM on a nonzero register.

local notation "FiniteMeasurement" => QAlgorithms.Papers.Independent.Information100.P04.Measurement

local notation "relative" =>
  ((fun _ _ rho => RE rho) : ExtendedEntanglementFunctional)

-- Reuse the accepted operational/variational quantity through a typed notation.

local notation "squashed" =>
  ((fun _ _ rho => ENNReal.ofReal (SQ rho)) : ExtendedEntanglementFunctional)

local notation "originalMarginal" => QAlgorithms.Papers.Independent.Information100.P04.principalMarginal

-- Exact accepted partial trace of the same AA'BB' extension.

local notation "ancillaryMarginal" => QAlgorithms.Papers.Independent.Information100.P04.ancillaryMarginal

local notation "distillable" =>
  ((fun _ _ rho => ENNReal.ofReal (QAlgorithms.Papers.Independent.Gap48.P32.twoWayDistillable rho)) : ExtendedEntanglementFunctional)

local notation "cost" =>
  ((fun _ _ rho => ENNReal.ofReal (QAlgorithms.Papers.Independent.Dependency50.P42.alternativeCost
    (fun _ _ X Y => traceNorm (X-Y)) rho)) : ExtendedEntanglementFunctional)

/-- Unnumbered further separations, PDF pp.15--16: seven displayed pairs,
the two known directions highlighted on p.15, and a bound-entangled witness
separating E_r,rightArrow^infinity from E_d, as printed on p.16.
Every existential has its own state and finite dimensions. -/
theorem further_entanglement_separations :
    StrictSeparation cost (fun _ _ rho => regularized relative rho) ∧
    StrictSeparation (fun _ _ rho => regularized classicalSquashed rho)
      (fun _ _ rho => regularized relative rho) ∧
    StrictSeparation (fun _ _ rho => regularized relative rho)
      (fun _ _ rho => regularized updated rho) ∧
    StrictSeparation (fun _ _ rho => regularized relative rho) key ∧
    StrictSeparation conditionalEntanglement (fun _ _ rho => regularized (measuredEntanglement .LOCC) rho) ∧
    StrictSeparation squashed (fun _ _ rho => regularized updated rho) ∧
    StrictSeparation squashed key ∧
    StrictSeparation conditionalEntanglement relative ∧
    StrictSeparation squashed (fun _ _ rho => regularized (measuredEntanglement .LOCC) rho) ∧
    (∃ a b : ℕ+, ∃ rho : Bipartite a b, IsDensityMatrix rho ∧
      rho ∉ separable a b ∧ Regularizes updated rho ∧
      distillable a b rho = 0 ∧ 0 < regularized updated rho) := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P16
