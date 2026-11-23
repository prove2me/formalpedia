-- Prove2me | Theorems.Thm_P2M_Formalism_ELL_FormalGroupPointsHom_evalMv2_zero__d743f55ca61b
-- name    : P2M_Formalism_ELL_FormalGroupPointsHom_evalMv2_zero__d743f55ca61b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:26:18.205282+00:00
-- url     : https://prove2.me/theorems/157057a9-6d26-4bee-9c1b-6c11b590fd06
-- title:
--   P2 M Formalism ELL Formal Group Points Hom eval Mv2 zero  d743f55ca61b: P2 M Formalism ELL Formal Group Points Hom eval Mv2 zero  d743f55ca61b
-- statement:
--   The P2 M Formalism ELL Formal Group Points Hom eval Mv2 zero  d743f55ca61b construction uses the P2 M Formalism ELL Formal Group Points Hom eval Mv2 zero  d743f55ca61b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L278-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L278-L279

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
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
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsHom
open Formalism.ELL Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem P2M_Formalism_ELL_FormalGroupPointsHom_evalMv2_zero__d743f55ca61b (a b : K) : evalMv2 (0 : MvPowerSeries (Fin 2) K) a b = 0 := by sorry

alias «Formalism».«ELL».«FormalGroupPointsHom».«evalMv2_zero'» := P2M_Formalism_ELL_FormalGroupPointsHom_evalMv2_zero__d743f55ca61b
