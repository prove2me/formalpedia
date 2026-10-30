-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIII_entry_2_1_1
-- name    : RamanujanLostNotebook.PartIII.entry_2_1_1
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-11T08:26:36.715532+00:00
-- url     : https://prove2.me/theorems/3aa4c44e-0582-41af-b841-e409465b1436
-- title:
--   Fifth-root crank dissection
-- statement:
--   P(a,v)=(a;v)_∞=∏_{k≥0}(1−av^k). F(z,v)=P(v,v)/[P(zv,v)P(v/z,v)]. G(v)=1/[P(v,v^5)P(v^4,v^5)]. H(v)=1/[P(v^2,v^5)P(v^3,v^5)]. A(v)=P(v^5,v^5)G(v)^2/H(v). B(v)=P(v^5,v^5)G(v). C(v)=P(v^5,v^5)H(v). D(v)=P(v^5,v^5)H(v)^2/G(v). For any primitive fifth root ζ and complex q with |q|<1, F(ζ,q)=A(q⁵)−(ζ+ζ⁻¹)²qB(q⁵)+(ζ²+ζ⁻²)q²C(q⁵)−(ζ+ζ⁻¹)q³D(q⁵).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 2, Entry 2.1.1, p. 10, eq. (2.1.6).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch02_crankProd
import Definitions.Def_RamanujanLostNotebook_PartIII_ch02_dissA
import Definitions.Def_RamanujanLostNotebook_PartIII_ch02_dissB
import Definitions.Def_RamanujanLostNotebook_PartIII_ch02_dissC
import Definitions.Def_RamanujanLostNotebook_PartIII_ch02_dissD
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_qPochInf
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_rrGProd
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_rrHProd

namespace RamanujanLostNotebook.PartIII
theorem entry_2_1_1 (ζ q : ℂ) (hζ : IsPrimitiveRoot ζ 5) (hq : ‖q‖ < 1) :
    crankProd ζ q =
      dissA (q ^ 5) - (ζ + ζ⁻¹) ^ 2 * q * dissB (q ^ 5) + (ζ ^ 2 + ζ⁻¹ ^ 2) * q ^ 2 * dissC (q ^ 5)
        - (ζ + ζ⁻¹) * q ^ 3 * dissD (q ^ 5) := by sorry
end RamanujanLostNotebook.PartIII
