-- Prove2me | Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_D__inv_5f24521fe641
-- name    : P2M_GroupTheoreticShannonCapacity_MAlpha_D__inv_5f24521fe641
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:33.762679+00:00
-- url     : https://prove2.me/theorems/ca43b867-c521-49e0-a883-e200cfd686c9
-- title:
--   P2 M Group Theoretic Shannon Capacity MAlpha D  inv 5f24521fe641: P2 M Group Theoretic Shannon Capacity MAlpha D  inv 5f24521fe641
-- statement:
--   D_β⁻¹ = D_{β⁻¹} when β ≠ 0
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean#L708-L722
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean#L708-L722

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MAlpha
open Matrix

theorem P2M_GroupTheoreticShannonCapacity_MAlpha_D__inv_5f24521fe641 (n : ℕ) (β : ℝ) (hβ : β ≠ 0) :
    (Dα n β)⁻¹ = Dα n (β⁻¹) := by sorry

alias «GroupTheoreticShannonCapacity».«MAlpha».«Dα_inv» := P2M_GroupTheoreticShannonCapacity_MAlpha_D__inv_5f24521fe641
