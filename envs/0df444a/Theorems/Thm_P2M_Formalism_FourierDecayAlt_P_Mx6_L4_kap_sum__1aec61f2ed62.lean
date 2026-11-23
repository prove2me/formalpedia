-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Mx6_L4_kap_sum__1aec61f2ed62
-- name    : P2M_Formalism_FourierDecayAlt_P_Mx6_L4_kap_sum__1aec61f2ed62
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:25:40.41002+00:00
-- url     : https://prove2.me/theorems/535e654f-0e87-428a-b5c4-7fb33e5e899e
-- title:
--   P2 M Formalism Fourier Decay Alt P Mx6 L4 kap sum  1aec61f2ed62: P2 M Formalism Fourier Decay Alt P Mx6 L4 kap sum  1aec61f2ed62
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Mx6 L4 kap sum  1aec61f2ed62 construction uses the P2 M Formalism Fourier Decay Alt P Mx6 L4 kap sum  1aec61f2ed62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1261-L1266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L1261-L1266

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.L4
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)

theorem P2M_Formalism_FourierDecayAlt_P_Mx6_L4_kap_sum__1aec61f2ed62 (s : Finset ℕ) (f : ℕ → Ty P → ℂ) :
    kap P (fun π => ∑ l ∈ s, f l π) = ∑ l ∈ s, kap P (f l) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Mx6».«L4».«kap_sum'» := P2M_Formalism_FourierDecayAlt_P_Mx6_L4_kap_sum__1aec61f2ed62
