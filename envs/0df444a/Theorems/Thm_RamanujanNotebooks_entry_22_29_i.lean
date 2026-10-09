-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_22_29_i
-- name    : RamanujanNotebooks.entry_22_29_i
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T21:54:51.530993+00:00
-- url     : https://prove2.me/theorems/4e767525-b278-431f-96a8-8a641b588bbc
-- title:
--   cbrt(cos 40°) + cbrt(cos 80°) - cbrt(cos 20°) = cbrt((3/2)(cbrt 9 - 2))
-- statement:
--   With real cube roots: $\sqrt[3]{\cos\tfrac{2\pi}9}+\sqrt[3]{\cos\tfrac{4\pi}9}-\sqrt[3]{\cos\tfrac{\pi}9}=\sqrt[3]{\tfrac32\bigl(\sqrt[3]9-2\bigr)}$.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part IV (Springer, 1994), Chapter 22, Entry 29, p. 39, eq. (29.1).

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_realCbrt

namespace RamanujanNotebooks
theorem entry_22_29_i :
    realCbrt (Real.cos (2 * Real.pi / 9)) + realCbrt (Real.cos (4 * Real.pi / 9)) -
        realCbrt (Real.cos (Real.pi / 9)) =
      realCbrt (3 / 2 * (realCbrt 9 - 2)) := by sorry
end RamanujanNotebooks
