-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P01_tic_tac_toe_construction
-- name    : QAlgorithms.Papers.Independent.Extend50.P01.tic_tac_toe_construction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:44:13.614189+00:00
-- url     : https://prove2.me/theorems/a97df4f5-bd6e-42fd-a431-16d4bf4a470a
-- title:
--   §V tic-tac-toe: D4-invariant nine-qubit prediction model
-- statement:
--   Number the perimeter sites $0,\ldots,7$ with even corners and odd edges, and center $8$. A quarter turn and the vertical reflection $(02)(73)(64)$ generate the eight-element board group $D_4$, represented by the wire permutations. Encode board data $g_i\in\{-1,0,1\}$ by $\bigotimes_iR_X(2\pi g_i/3)$ and initialize $|0^9\rangle$. In each complete trainable block use shared corner/edge/center one-qubit unitaries, followed by complete commuting controlled-$R_Y$ layers corner-to-neighboring-edge, edge-to-center and center-to-corner. Their parameters and the number of re-uploading layers are arbitrary. Define $O_\circ=(Z_0+Z_2+Z_4+Z_6)/4$, $O_-=Z_8$, and $O_\times=(Z_1+Z_3+Z_5+Z_7)/4$. The blocks commute with the represented group, the input and observables are invariant, and
--   $$\widehat y(\sigma g)=\widehat y(g)\quad(\sigma\in D_4),\qquad\widehat y=(\langle O_\circ\rangle,\langle O_-\rangle,\langle O_\times\rangle).$$
--   The entire prediction vector is invariant, so no tie-breaking convention is required. The single-qubit factor in every complete block is RY(theta[c,1]) RX(theta[c,0]) for the vertex class c, with two real angles per class shared on all its sites, exactly as in Figure 3. The nine real angles of a board block consist of these six angles and three controlled-Y orbit angles; a vehicle block has these six angles and four controlled-Z orbit angles.
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, PDF p. 11, §V tic-tac-toe: D4-invariant nine-qubit prediction model

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

/-- PDF pp.11–13, Fig.3 and Eqs.(88)–(90): the constructed nine-qubit D4-invariant predictor.
Orbit rotations are complete commuting layers; arbitrary overlapping sequential layouts are excluded. -/
theorem tic_tac_toe_construction
    (W : List (List ((Fin 3 → Fin 2 → ℝ) × (Fin 3 → ℝ)))) :
    boardGroup.carrier.ncard = 8 ∧
    (∀ s ∈ boardGroup, ∀ t ∈ boardGroup, wireMatrix (s * t) = wireMatrix s * wireMatrix t) ∧
    (∀ s ∈ boardGroup, wireMatrix s ∈ Matrix.unitaryGroup (Qubits 9) ℂ ∧
      act (wireMatrix s) (zeroKet 9) = zeroKet 9 ∧
      (∀ p, Commute (boardLayer p) (wireMatrix s)) ∧
      (∀ a, conjugate (wireMatrix s) (boardObservable a) = boardObservable a)) ∧
    (∀ x : Fin 9 → ℝ, (∀ i, x i ∈ ({-1,0,1} : Set ℝ)) → ∀ s ∈ boardGroup,
      boardPrediction W (featurePullback s x) = boardPrediction W x) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P01

end
