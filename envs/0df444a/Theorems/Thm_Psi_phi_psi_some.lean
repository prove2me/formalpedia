-- Prove2me | Theorems.Thm_Psi_phi_psi_some
-- name    : Psi.phi_psi_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:17:27.676058+00:00
-- url     : https://prove2.me/theorems/473aca6e-a4ba-45e6-9768-955c7a7aed95
-- title:
--   Psi: phi psi some
-- statement:
--   The `some`-branch (a `DD` exists) of the surjectivity round-trip.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L618-L671
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L618-L671

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.phi_psi_some (n : ℕ)
    (IH : ∀ m, m < n → ∀ π : List Bool, π.length = m → IsDyck π → π ≠ [] →
      phiPath (psiPath π).1 (psiPath π).2 = π)
    (π : List Bool) (hlen : π.length = n) (hd : IsDyck π) (hne : π ≠ []) (i : ℕ)
    (hfd : firstDDidx (π.drop (2 * cUD π + 1)) = some i) :
    phiPath (psiPath π).1 (psiPath π).2 = π := by sorry
