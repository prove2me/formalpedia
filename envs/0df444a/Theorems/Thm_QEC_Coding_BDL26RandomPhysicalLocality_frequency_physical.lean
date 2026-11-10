-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_frequency_physical
-- name    : QEC.Coding.BDL26RandomPhysicalLocality.frequency_physical
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T02:25:56.423943+00:00
-- url     : https://prove2.me/theorems/71c978fa-edcb-4bdc-8517-695eb3c14f4b
-- title:
--   BDL26 Random Physical Locality: frequency physical
-- statement:
--   The metric conclusion concerns exactly the subsystem of the full-H frequency.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalLocality.lean#L159-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalLocality.lean#L159-L170

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPhysicalLocality
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open BDL26TannerLocalRegularity
open BDL26QuantitativeBounds BDL26DecodingGraph BDL26CSSHamiltonian
open Semantics Semantics.Davies
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26RandomPhysicalLocality.frequency_physical (S : OddScale) (n : Nat)
    (J : Vertex (state S n).presentation → E) {t : ℝ}
    (hJ : IsBoundedDensityLocalMap (state S n).presentation J t)
    (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    (BDL26CSSDaviesLocality.subsystem S n q).OperatorSupportedOnRegister
      (actualFrequency (hamiltonian S n) (BDL26CSSDaviesLocality.hamiltonian_symmetric S n)
        (BDL26CSSDaviesLocality.coupling S n q a) ω) ∧
    (∀ r ∈ region S n q, dist (J (.q r)) (J (.q q)) ≤ 2) ∧
    (∀ r ∈ region S n q, ∀ s ∈ region S n q, dist (J (.q r)) (J (.q s)) ≤ 4) ∧
    (BDL26CSSDaviesLocality.subsystem S n q).selected.card ≤ 50 := by sorry
