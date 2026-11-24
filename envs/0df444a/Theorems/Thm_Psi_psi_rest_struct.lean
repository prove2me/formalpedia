-- Prove2me | Theorems.Thm_Psi_psi_rest_struct
-- name    : Psi.psi_rest_struct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:03:28.18781+00:00
-- url     : https://prove2.me/theorems/2648000c-31fb-4cb6-9d66-cb8cde937c7c
-- title:
--   Psi: psi rest struct
-- statement:
--   **Run-structure decomposition** (`some`-branch of `Ψ`): if `rest` starts with a
--   North step and has a first `DD` at index `i`, then with `b`, `ρ = rest.take (i-b)`,
--   `ρ' = rest.drop (i+b+1)` as `Ψ` extracts, `rest = ρ U^b D^{b+1} ρ'` with `ρ` `DD`-free,
--   the maximality condition, `b ≥ 1`, and `ρ` `[]` or starting North.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L175-L254
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L175-L254

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.psi_rest_struct (rest : List Bool) (i p L b : ℕ)
    (h : firstDDidx rest = some i) (hstart : rest.head? = some true)
    (hp : p = ((rest.take i).reverse.takeWhile id).length)
    (hL : L = ((rest.drop i).takeWhile (· = false)).length)
    (hb : b = min p (L - 1)) :
    rest = rest.take (i - b) ++ List.replicate b true ++ List.replicate (b + 1) false
             ++ rest.drop (i + b + 1)
      ∧ hasDD (rest.take (i - b)) = false
      ∧ ((rest.take (i - b)).getLast? ≠ some true ∨ (rest.drop (i + b + 1)).head? ≠ some false)
      ∧ 1 ≤ b
      ∧ (numN (rest.take (i - b)) = 0 → rest.take (i - b) = []) := by sorry
