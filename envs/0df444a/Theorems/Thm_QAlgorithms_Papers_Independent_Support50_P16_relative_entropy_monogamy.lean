-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P16_relative_entropy_monogamy
-- name    : QAlgorithms.Papers.Independent.Support50.P16.relative_entropy_monogamy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:57:09.771016+00:00
-- url     : https://prove2.me/theorems/dd06549f-e432-483a-9d76-3baa0cd2aec9
-- title:
--   Theorem 1, Eqs. (6)–(7): relative-entropy monogamy
-- statement:
--   Let $\rho_{ABE}$ be any density matrix on three nonzero finite-dimensional complex registers. All displayed reduced states are actual partial traces. Let $E_r$ denote the relative entropy distance to separable states across the indicated bipartition, and let $E_{r,1\text{-LOCC}}$ use measurements from $A$ to $B$. Superscript $\infty$ denotes per-copy regularization, with copies grouped by laboratory. In bits,
--
--   $$
--   \begin{aligned}
--   E_r(\rho_{B:AE})&\ge E_{r,1\text{-LOCC}}(\rho_{AB})+E_r^\infty(\rho_{BE}),\\
--   E_r^\infty(\rho_{B:AE})&\ge E_{r,1\text{-LOCC}}^\infty(\rho_{AB})+E_r^\infty(\rho_{BE}).
--   \end{aligned}
--   $$
--
--   The same register $B$ occurs in both right-hand terms. The one-way regularization limit exists. This weak monogamy relation needs no separability or purity of the input.
-- source:
--   Relative entropy and squashed entanglement, arXiv:1210.3181v2, PDF p. 4, Theorem 1, Eqs. (6)–(7): relative-entropy monogamy

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

/-- Theorem 1, Eqs.(6)--(7), PDF p.4; proof pp.8--9. B is repeated, not split. -/
theorem relative_entropy_monogamy {a b e : ℕ+}
    (rho : Matrix ((Fin (a : ℕ) × Fin (b : ℕ)) × Fin (e : ℕ))
      ((Fin (a : ℕ) × Fin (b : ℕ)) × Fin (e : ℕ)) ℂ)
    (hrho : IsDensityMatrix rho) :
    let AB := traceRight rho
    let BE := traceLeft (QAlgorithms.Papers.Independent.Dependency50.P19.associate rho)
    Regularizes (measuredEntanglement .oneWay) AB ∧
    measuredEntanglement .oneWay a b AB + RER BE ≤ RE (cutBAE rho) ∧
    regularized (measuredEntanglement .oneWay) AB + RER BE ≤ RER (cutBAE rho) := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P16
