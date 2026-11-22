-- Prove2me | Theorems.Thm_WeakOrderUnit_of_strongOrderUnit
-- name    : WeakOrderUnit.of_strongOrderUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:17:38.393054+00:00
-- url     : https://prove2.me/theorems/4517e061-0b96-4312-ba10-701eebfa9c45
-- title:
--   Weak Order Unit: of strong Order Unit
-- statement:
--   Every strong order unit is a weak order unit.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderUnit.lean#L58-L68
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderUnit.lean#L58-L68

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderUnit
set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

theorem WeakOrderUnit.of_strongOrderUnit {e : X} (he : StrongOrderUnit e) :
    WeakOrderUnit e := by sorry
