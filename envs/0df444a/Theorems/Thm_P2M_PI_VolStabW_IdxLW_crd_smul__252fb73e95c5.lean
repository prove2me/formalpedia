-- Prove2me | Theorems.Thm_P2M_PI_VolStabW_IdxLW_crd_smul__252fb73e95c5
-- name    : P2M_PI_VolStabW_IdxLW_crd_smul__252fb73e95c5
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:04:32.535683+00:00
-- url     : https://prove2.me/theorems/70ff11d7-d062-46ac-a1ae-912906b721ef
-- title:
--   P2 M PI Vol Stab W Idx LW crd smul  252fb73e95c5: P2 M PI Vol Stab W Idx LW crd smul  252fb73e95c5
-- statement:
--   The P2 M PI Vol Stab W Idx LW crd smul  252fb73e95c5 construction uses the P2 M PI Vol Stab W Idx LW crd smul  252fb73e95c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensHIL.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensHIL.lean#L49-L52

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHI
import Definitions.Def_ReciprocityTheory_Automorphisms_InstMainA
import Definitions.Def_ReciprocityTheory_ResidueCardinality_ArtinOntoB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHIL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.IdxLW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsLocalRing
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (a M : ℕ)

theorem P2M_PI_VolStabW_IdxLW_crd_smul__252fb73e95c5 (s : Fv F v) (y : Fv F v ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (s • y) k =
      s * (Algebra.TensorProduct.basis (Fv F v) b).repr y k := by sorry

alias «PI».«VolStabW».«IdxLW».«crd_smul'» := P2M_PI_VolStabW_IdxLW_crd_smul__252fb73e95c5
