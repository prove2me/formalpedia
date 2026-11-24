-- Prove2me | Theorems.Thm_Psi_psiPath_step
-- name    : Psi.psiPath_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:59:27.541615+00:00
-- url     : https://prove2.me/theorems/5d7e88d5-dc1a-4463-8b3b-f020e086beef
-- title:
--   Psi: psi Path step
-- statement:
--   `Ψ` on a recursive path `(UD)^a U ρ U^b D^{b+1} ρ'` peels off the block
--   `0^a 1^b 0` and area entry `numN ρ`, recursing on `ρ ++ ρ'`.  Requires: `b ≥ 1`,
--   `ρ` starts with a North step (or is empty), `ρ` has no `DD`, the maximality
--   condition, and `ρ ++ ρ'` nonempty.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L471-L541
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L471-L541

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
set_option autoImplicit true
open Psi

theorem Psi.psiPath_step (a b : ℕ) (ρ ρ' : List Bool)
    (hb : 1 ≤ b)
    (hρU : ρ = [] ∨ ρ.head? = some true)
    (hρDD : hasDD ρ = false)
    (hmax : ρ.getLast? ≠ some true ∨ ρ'.head? ≠ some false)
    (hne : ρ ++ ρ' ≠ []) :
    psiPath ((List.replicate a [true, false]).flatten ++ [true] ++ ρ
              ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ')
      = (List.replicate a false ++ List.replicate b true ++ [false] ++ (psiPath (ρ ++ ρ')).1,
         numN ρ :: (psiPath (ρ ++ ρ')).2) := by sorry
