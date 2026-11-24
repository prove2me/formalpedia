-- Prove2me | Theorems.Thm_Psi_psi_valid_head_some
-- name    : Psi.psi_valid_head_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:18:23.861251+00:00
-- url     : https://prove2.me/theorems/8afb912b-2f41-4183-92ed-f3aa54d0fd55
-- title:
--   Psi: psi valid head some
-- statement:
--   The `some`-branch of the well-definedness induction: `Ψ π` is valid and its
--   first height coordinate is `numNBeforeDD π`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L262-L339
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L262-L339

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
set_option autoImplicit true
open Psi

theorem Psi.psi_valid_head_some (n : ℕ)
    (IH : ∀ m, m < n → ∀ π : List Bool, π.length = m → IsDyck π → π ≠ [] →
      IsValid (psiPath π).1 (psiPath π).2 ∧
        (tauOf (psiPath π).1 (psiPath π).2).headD 0 = numNBeforeDD π)
    (π : List Bool) (hlen : π.length = n) (hd : IsDyck π) (hne : π ≠ []) (i : ℕ)
    (hfd : firstDDidx (π.drop (2 * cUD π + 1)) = some i) :
    IsValid (psiPath π).1 (psiPath π).2 ∧
      (tauOf (psiPath π).1 (psiPath π).2).headD 0 = numNBeforeDD π := by sorry
