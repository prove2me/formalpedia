-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P01_heisenberg_twirl
-- name    : QAlgorithms.Papers.Independent.Extend50.P01.heisenberg_twirl
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:48:42.463024+00:00
-- url     : https://prove2.me/theorems/8c70d8de-1ab9-445a-8348-f64bd176c766
-- title:
--   §V Eqs.(104)–(109): collective SU(2) generator twirling
-- statement:
--   Let $N\ge2$, and average conjugation by $V^{\otimes N}$ over normalized Haar measure on $SU(2)$. For distinct sites $i,j$ and any Pauli axis $a\in\{X,Y,Z\}$, the integrand is integrable and
--   $$T(a_ia_j)=\frac{X_iX_j+Y_iY_j+Z_iZ_j}{3}=-\frac13I+\frac23\mathrm{SWAP}_{ij}.$$
--   The identities act on all spectator wires. Each single-site $Y_i$ integrand is also integrable and $T(Y_i)=0$. This gives the exact normalization behind the source's effective isotropic generator, which it states only up to scale and irrelevant scalar identity terms.
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, PDF p. 18, §V Eqs.(104)–(109): collective SU(2) generator twirling

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

local notation "parity" => (fun n : ℕ => QAlgorithms.Papers.Independent.Information100.P69.matrixPower pauliX n)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P01.su2MeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P01.su2BorelSpace

local notation "collective" => (fun (n : ℕ) (V : SU2) => QAlgorithms.Papers.Independent.Information100.P69.matrixPower (Subtype.val V) n)

/-- PDF p.18, Eqs.(104)–(109): exact normalized value is isotropic interaction divided by 3.
Spectator identities in Eq.(105) are restored, and the source's proportionality is not an equality. -/
theorem heisenberg_twirl (N : ℕ) (hN : 2 ≤ N) (mu : Measure SU2)
    [Measure.IsHaarMeasure mu] [IsProbabilityMeasure mu] :
    (∀ (i j : Fin N), i ≠ j → ∀ a : Fin 3,
      Integrable (fun V => conjugate (collective N V) (onWire i (axis a) * onWire j (axis a))) mu ∧
      collectiveTwirl N mu (onWire i (axis a) * onWire j (axis a)) =
        (1 / 3 : ℂ) • (∑ b : Fin 3, onWire i (axis b) * onWire j (axis b)) ∧
      collectiveTwirl N mu (onWire i (axis a) * onWire j (axis a)) =
        (-1 / 3 : ℂ) • (1 : Op N) + (2 / 3 : ℂ) • wireMatrix (Equiv.swap i j)) ∧
    (∀ i : Fin N,
      Integrable (fun V => conjugate (collective N V) (onWire i pauliY)) mu ∧
      collectiveTwirl N mu (onWire i pauliY) = 0) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P01

end
