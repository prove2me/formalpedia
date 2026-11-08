-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalGridParity_strip_exists_boundary_eq_add_rootParity
-- name    : QEC.Coding.BDL26XLocalGridParity.strip_exists_boundary_eq_add_rootParity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:39:47.315695+00:00
-- url     : https://prove2.me/theorems/9ecf1470-ce40-4d93-a02f-0fad092bfe66
-- title:
--   BDL26 XLocal Grid Parity: strip exists boundary eq add root Parity
-- statement:
--   Strip cleanup uses only adjacent strip edges and retains its parity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalGridParity.lean#L73-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalGridParity.lean#L73-L80

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalGridParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalGridParity
open BDL26TannerLocalRegularity
open BDL26FiniteAlternatingCore

theorem QEC.Coding.BDL26XLocalGridParity.strip_exists_boundary_eq_add_rootParity
    (m : ℕ) (hm : 0 < m) (root : StripVertex m)
    (syndrome : Word (ZMod 2) (StripVertex m)) :
    ∃ correction : Word (ZMod 2) (StripEdge m),
      graphBoundary (stripStart m) (stripEnd m) correction =
        syndrome + Pi.single root (totalParity syndrome) := by sorry
