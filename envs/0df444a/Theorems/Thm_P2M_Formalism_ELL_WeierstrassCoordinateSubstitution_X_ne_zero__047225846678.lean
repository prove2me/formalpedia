-- Prove2me | Theorems.Thm_P2M_Formalism_ELL_WeierstrassCoordinateSubstitution_X_ne_zero__047225846678
-- name    : P2M_Formalism_ELL_WeierstrassCoordinateSubstitution_X_ne_zero__047225846678
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:02.008833+00:00
-- url     : https://prove2.me/theorems/230e3473-c398-4ce6-a13b-2396def395a8
-- title:
--   P2 M Formalism ELL Weierstrass Coordinate Substitution X ne zero  047225846678: P2 M Formalism ELL Weierstrass Coordinate Substitution X ne zero  047225846678
-- statement:
--   The P2 M Formalism ELL Weierstrass Coordinate Substitution X ne zero  047225846678 construction uses the P2 M Formalism ELL Weierstrass Coordinate Substitution X ne zero  047225846678 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExistsUnitFactor.lean#L143-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExistsUnitFactor.lean#L143-L146

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassCoordinateSubstitution
variable {K : Type u} [Field K]

theorem P2M_Formalism_ELL_WeierstrassCoordinateSubstitution_X_ne_zero__047225846678 {σ : Type} (i : σ) : (MvPowerSeries.X i : MvPowerSeries σ K) ≠ 0 := by sorry

alias «Formalism».«ELL».«WeierstrassCoordinateSubstitution».«X_ne_zero'» := P2M_Formalism_ELL_WeierstrassCoordinateSubstitution_X_ne_zero__047225846678
