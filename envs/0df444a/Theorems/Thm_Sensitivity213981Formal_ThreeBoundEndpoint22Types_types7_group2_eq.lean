-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Types_types7_group2_eq
-- name    : Sensitivity213981Formal.ThreeBoundEndpoint22Types.types7_group2_eq
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:47:06.937084+00:00
-- url     : https://prove2.me/theorems/62020449-d4bf-423f-ad79-f3272ef8500d
-- title:
--   Seven-kind prefix enumeration: group 2
-- statement:
--   Let $K$ be the finite kind type of the construction. Let $P$ be the fixed ordered list of prefix and order-key pairs in group 2, and let $T$ be the explicit table of seven-entry kind lists in the cited declaration. Then
--   $$\operatorname{concat}([\operatorname{filteredPrefix}(p,k,4)\mid(p,k)\in P])=T.$$
--   Every prefix, key, table entry, order and repetition is fixed by the formal statement. This exact list equality supplies the corresponding group in the seven-position finite coverage enumeration.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22Type7Group2.lean, lines 67–70.

import Definitions.Def_Sensitivity213981Formal_Endpoint22TypeData
import Definitions.Def_Sensitivity213981Formal_Endpoint22TypeSplit
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

namespace Sensitivity213981Formal
section
/- Exact bounded Type7 group. Generated source; requires Lean checking. -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Types
open ThreeBoundQ3 ThreeBoundEndpoint22TypeSplit

























































theorem _root_.Sensitivity213981Formal.ThreeBoundEndpoint22Types.types7_group2_eq :
    ((filteredPrefix ([2,2,2] : List Kind) (orderKey (2 : Kind)) 4 ++ filteredPrefix ([2,2,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([2,2,5] : List Kind) (orderKey (5 : Kind)) 4 ++ filteredPrefix ([2,2,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([2,2,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([2,2,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([2,2,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([2,3,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([2,3,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([2,3,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([2,3,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([2,5,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([2,5,5] : List Kind) (orderKey (5 : Kind)) 4 ++ filteredPrefix ([2,5,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([2,5,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([2,5,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([2,5,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([2,6,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([2,6,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([2,6,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([2,7,7] : List Kind) (orderKey (7 : Kind)) 4 ++ []) ++ (filteredPrefix ([2,9,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([2,9,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([2,9,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([2,9,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([2,9,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([2,10,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([2,10,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ []) =
      [[2,2,2,3,7,7,7],[2,2,2,6,7,7,7],[2,2,2,7,7,7,7],[2,2,2,10,7,7,7],[2,2,3,3,3,7,7],[2,2,3,3,6,7,7],[2,2,3,3,7,7,7],[2,2,3,3,10,7,7],[2,2,3,6,6,7,7],[2,2,3,6,7,7,7],[2,2,3,6,10,7,7],[2,2,3,7,7,7,7],[2,2,3,10,7,7,7],[2,2,3,10,10,7,7],[2,2,5,3,7,7,7],[2,2,5,6,7,7,7],[2,2,5,7,7,7,7],[2,2,5,10,7,7,7],[2,2,6,6,6,7,7],[2,2,6,6,7,7,7],[2,2,6,6,10,7,7],[2,2,6,7,7,7,7],[2,2,6,10,7,7,7],[2,2,6,10,10,7,7],[2,2,7,7,7,7,7],[2,2,9,3,7,7,7],[2,2,9,6,7,7,7],[2,2,9,7,7,7,7],[2,2,9,10,7,7,7],[2,2,10,7,7,7,7],[2,2,10,10,7,7,7],[2,2,10,10,10,7,7],[2,3,3,3,3,3,7],[2,3,3,3,3,6,7],[2,3,3,3,3,7,7],[2,3,3,3,3,10,7],[2,3,3,3,6,6,7],[2,3,3,3,6,7,7],[2,3,3,3,6,10,7],[2,3,3,3,7,7,7],[2,3,3,3,10,7,7],[2,3,3,3,10,10,7],[2,3,3,6,6,6,7],[2,3,3,6,6,7,7],[2,3,3,6,6,10,7],[2,3,3,6,7,7,7],[2,3,3,6,10,7,7],[2,3,3,6,10,10,7],[2,3,3,7,7,7,7],[2,3,3,10,7,7,7],[2,3,3,10,10,7,7],[2,3,3,10,10,10,7],[2,3,6,6,6,6,7],[2,3,6,6,6,7,7],[2,3,6,6,6,10,7],[2,3,6,6,7,7,7],[2,3,6,6,10,7,7],[2,3,6,6,10,10,7],[2,3,6,7,7,7,7],[2,3,6,10,7,7,7],[2,3,6,10,10,7,7],[2,3,6,10,10,10,7],[2,3,7,7,7,7,7],[2,3,10,7,7,7,7],[2,3,10,10,7,7,7],[2,3,10,10,10,7,7],[2,3,10,10,10,10,7],[2,5,3,3,3,7,7],[2,5,3,3,6,7,7],[2,5,3,3,7,7,7],[2,5,3,3,10,7,7],[2,5,3,6,6,7,7],[2,5,3,6,7,7,7],[2,5,3,6,10,7,7],[2,5,3,7,7,7,7],[2,5,3,10,7,7,7],[2,5,3,10,10,7,7],[2,5,5,3,7,7,7],[2,5,5,6,7,7,7],[2,5,5,7,7,7,7],[2,5,5,10,7,7,7],[2,5,6,6,6,7,7],[2,5,6,6,7,7,7],[2,5,6,6,10,7,7],[2,5,6,7,7,7,7],[2,5,6,10,7,7,7],[2,5,6,10,10,7,7],[2,5,7,7,7,7,7],[2,5,9,3,7,7,7],[2,5,9,6,7,7,7],[2,5,9,7,7,7,7],[2,5,9,10,7,7,7],[2,5,10,7,7,7,7],[2,5,10,10,7,7,7],[2,5,10,10,10,7,7],[2,6,6,6,6,6,7],[2,6,6,6,6,7,7],[2,6,6,6,6,10,7],[2,6,6,6,7,7,7],[2,6,6,6,10,7,7],[2,6,6,6,10,10,7],[2,6,6,7,7,7,7],[2,6,6,10,7,7,7],[2,6,6,10,10,7,7],[2,6,6,10,10,10,7],[2,6,7,7,7,7,7],[2,6,10,7,7,7,7],[2,6,10,10,7,7,7],[2,6,10,10,10,7,7],[2,6,10,10,10,10,7],[2,7,7,7,7,7,7],[2,9,3,3,3,7,7],[2,9,3,3,6,7,7],[2,9,3,3,7,7,7],[2,9,3,3,10,7,7],[2,9,3,6,6,7,7],[2,9,3,6,7,7,7],[2,9,3,6,10,7,7],[2,9,3,7,7,7,7],[2,9,3,10,7,7,7],[2,9,3,10,10,7,7],[2,9,6,6,6,7,7],[2,9,6,6,7,7,7],[2,9,6,6,10,7,7],[2,9,6,7,7,7,7],[2,9,6,10,7,7,7],[2,9,6,10,10,7,7],[2,9,7,7,7,7,7],[2,9,9,3,7,7,7],[2,9,9,6,7,7,7],[2,9,9,7,7,7,7],[2,9,9,10,7,7,7],[2,9,10,7,7,7,7],[2,9,10,10,7,7,7],[2,9,10,10,10,7,7],[2,10,7,7,7,7,7],[2,10,10,7,7,7,7],[2,10,10,10,7,7,7],[2,10,10,10,10,7,7],[2,10,10,10,10,10,7]] := by sorry
end ThreeBoundEndpoint22Types


end
end Sensitivity213981Formal
