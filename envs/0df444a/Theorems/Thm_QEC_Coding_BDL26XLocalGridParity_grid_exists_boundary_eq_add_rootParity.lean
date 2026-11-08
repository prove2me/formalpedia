-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalGridParity_grid_exists_boundary_eq_add_rootParity
-- name    : QEC.Coding.BDL26XLocalGridParity.grid_exists_boundary_eq_add_rootParity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:39:39.143101+00:00
-- url     : https://prove2.me/theorems/d34da548-0693-4738-b681-6bb4f55f258f
-- title:
--   BDL26 XLocal Grid Parity: grid exists boundary eq add root Parity
-- statement:
--   Grid cleanup uses only adjacent grid edges and retains its parity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalGridParity.lean#L83-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalGridParity.lean#L83-L90

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalGridParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalGridParity
open BDL26TannerLocalRegularity
open BDL26FiniteAlternatingCore

theorem QEC.Coding.BDL26XLocalGridParity.grid_exists_boundary_eq_add_rootParity
    (m : ℕ) (hm : 0 < m) (root : GridVertex m)
    (syndrome : Word (ZMod 2) (GridVertex m)) :
    ∃ correction : Word (ZMod 2) (GridEdge m),
      graphBoundary (gridStart m) (gridEnd m) correction =
        syndrome + Pi.single root (totalParity syndrome) := by sorry
