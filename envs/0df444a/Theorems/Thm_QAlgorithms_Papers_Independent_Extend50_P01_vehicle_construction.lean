-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P01_vehicle_construction
-- name    : QAlgorithms.Papers.Independent.Extend50.P01.vehicle_construction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:45:14.481408+00:00
-- url     : https://prove2.me/theorems/f56a20a5-d755-4dfa-8a6c-8c83676f06cb
-- title:
--   §V autonomous vehicle: C4-invariant nine-qubit regression model
-- statement:
--   On the same nine-site board, let $x_i\in\{1,-1,-1/3,1/3\}$ encode the scene, including the vehicle and its orientation. Encode with $R_X(2\pi x_i/3)$ on each site, initialize $|0^9\rangle$, and use shared corner/edge/center one-qubit unitaries and controlled-$R_Z$ orbit layers. Clockwise and counterclockwise corner-to-edge operations have distinct shared coordinates. The quarter turn generates a four-element rotation group $C_4$; each complete trainable block commutes with its wire action. For arbitrary parameters and re-uploading depth, the scalar output satisfies
--   $$\widehat y(x)=\frac{\langle Z_8\rangle+1}{2}\in[0,1],\qquad \widehat y(\sigma x)=\widehat y(x)\quad(\sigma\in C_4).$$
--   This is rotational invariance of the constructed regression model; no mirror invariance or empirical learning advantage is asserted. The single-qubit factor in every complete block is RY(theta[c,1]) RX(theta[c,0]) for the vertex class c, with two real angles per class shared on all its sites, exactly as in Figure 3. The nine real angles of a board block consist of these six angles and three controlled-Y orbit angles; a vehicle block has these six angles and four controlled-Z orbit angles.
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, PDF p. 15, §V autonomous vehicle: C4-invariant nine-qubit regression model

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P01

noncomputable section

open scoped Matrix Kronecker ComplexConjugate Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P01

attribute [local instance] Classical.propDecidable Classical.decEq

-- PDF pp.3,8: reuse the accepted operator type, exp(-itH), and A X A†.
-- Notation specializes the imported interfaces without introducing duplicate declarations.

local notation "Op" => (fun n : ℕ => QAlgorithms.Papers.Independent.Information100.P21.Op (Qubits n))

local notation "evolve" => QAlgorithms.Papers.Independent.Information100.P32.evolution

local notation "conjugate" => QAlgorithms.conjSuperop

-- PDF pp.3,10–11: the imported quadratic form is Re(psi† A psi).

local notation "expectation" => QAlgorithms.Papers.Independent.Information100.P21.quad

-- PDF pp.5,16–19: accepted active-wire operator, with identities on all spectators.

local notation "onWire" => QAlgorithms.Papers.Independent.Advance50.P49.onWire

-- PDF p.5: the imported phase-free Pauli tensor uses 0=I,1=X,2=Y,3=Z.

local notation "pauliWord" => QAlgorithms.Papers.Independent.Gap48.P33.pauliWord

/-- PDF pp.14–15, Eq.(92): quarter-turn invariance and output interval of the vehicle model.
Only the rotation group is used, and car orientations rotate as part of the scenario array. -/
theorem vehicle_construction
    (W : List (List ((Fin 3 → Fin 2 → ℝ) × (Fin 4 → ℝ)))) :
    vehicleGroup.carrier.ncard = 4 ∧
    (∀ s ∈ vehicleGroup, ∀ p, Commute (vehicleLayer p) (wireMatrix s)) ∧
    (∀ x : Fin 9 → ℝ, (∀ i, x i ∈ ({1,-1,-(1/3),1/3} : Set ℝ)) →
      vehiclePrediction W x ∈ Set.Icc 0 1 ∧ ∀ s ∈ vehicleGroup,
        vehiclePrediction W (featurePullback s x) = vehiclePrediction W x) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P01

end
