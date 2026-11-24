-- Prove2me | Theorems.Thm_Psi_psi_phi
-- name    : Psi.psi_phi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:15:16.411684+00:00
-- url     : https://prove2.me/theorems/b16364cc-4104-425b-bedb-8cba63268393
-- title:
--   Psi: psi phi
-- statement:
--   Round-trip `Ψ ∘ Φ = id` on valid data (the injectivity content).
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L544-L605
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L544-L605

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
set_option autoImplicit true
open Psi

theorem Psi.psi_phi (w : List Bool) (av : List ℕ) (h : IsValid w av) :
    psiPath (phiPath w av) = (w, av) := by sorry
