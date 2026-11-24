-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exists_adelic_neg_one_387b409f59b6
-- name    : P2M_Formalism_BasicNotions_Examples__exists_adelic_neg_one_387b409f59b6
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:35:38.656209+00:00
-- url     : https://prove2.me/theorems/05890890-2c47-4e73-938a-4c383b5b37f4
-- title:
--   P2 M Formalism Basic Notions Examples  exists adelic neg one 387b409f59b6: P2 M Formalism Basic Notions Examples  exists adelic neg one 387b409f59b6
-- statement:
--   The P2 M Formalism Basic Notions Examples  exists adelic neg one 387b409f59b6 construction uses the P2 M Formalism Basic Notions Examples  exists adelic neg one 387b409f59b6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Adelic.lean#L539-L571
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Adelic.lean#L539-L571

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Adelic
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain HeightOneSpectrum IsLocalRing WithZero NumberField Filter Topology
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open scoped TensorProduct
variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)

theorem P2M_Formalism_BasicNotions_Examples__exists_adelic_neg_one_387b409f59b6 (σ : H.E →ₐ[H.F] H.E) (hσ : ∀ x, σ x = H.conj x) :
    ∃ y : H.E ⊗[H.F] FiniteAdeleRing (𝓞 H.F) H.F,
      Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 H.F) H.F) y * y = -1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«exists_adelic_neg_one» := P2M_Formalism_BasicNotions_Examples__exists_adelic_neg_one_387b409f59b6
