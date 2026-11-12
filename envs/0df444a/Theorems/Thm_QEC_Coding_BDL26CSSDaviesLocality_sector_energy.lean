-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_sector_energy
-- name    : QEC.Coding.BDL26CSSDaviesLocality.sector_energy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T17:38:15.53986+00:00
-- url     : https://prove2.me/theorems/0c27c565-8f54-4179-bd33-c23d841fea2d
-- title:
--   BDL26 CSSDavies Locality: sector energy
-- statement:
--   The same literal full-H sector energy, counting all labels with multiplicity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L110-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L110-L116

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26CSSDaviesLocality.sector_energy (u : Word (ZMod 2) (ZLabel S n))
    (v : Word (ZMod 2) (XLabel S n)) :
    BDL26CSSHamiltonian.hamiltonian S n * projector S n (CSSGibbs.joinSyndrome u v) =
      (((-((Fintype.card (ZLabel S n) + Fintype.card (XLabel S n) : Nat) : ℝ) +
        2 * ((HammingWeight u : ℝ) + (HammingWeight v : ℝ))) : ℝ) : ℂ) •
          projector S n (CSSGibbs.joinSyndrome u v) := by sorry
