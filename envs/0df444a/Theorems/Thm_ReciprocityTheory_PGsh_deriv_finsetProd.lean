-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_deriv_finsetProd
-- name    : ReciprocityTheory.PGsh.deriv_finsetProd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:33.446277+00:00
-- url     : https://prove2.me/theorems/8c451f10-0fb5-432a-98be-9660de413aba
-- title:
--   PGsh: deriv finset Prod
-- statement:
--   The PGsh construction uses the deriv finset Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L13-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L13-L27

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem ReciprocityTheory.PGsh.deriv_finsetProd {ι : Type*} [DecidableEq ι] (D : Derivation R A A) (t : Finset ι)
    (P : ι → A) :
    D (∏ k ∈ t, P k) = ∑ k₀ ∈ t, ∏ k ∈ t, (if k = k₀ then D (P k) else P k) := by sorry
