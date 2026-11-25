-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_ker_comp_redHom_ce1e3b93be1e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_ker_comp_redHom_ce1e3b93be1e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:11:52.392706+00:00
-- url     : https://prove2.me/theorems/3bc17599-c205-573e-be26-68140b983c48
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict ker comp red Hom ce1e3b93be1e: P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict ker comp red Hom ce1e3b93be1e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict ker comp red Hom ce1e3b93be1e construction uses the P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict ker comp red Hom ce1e3b93be1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L331-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L331-L347

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrLenRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_ker_comp_redHom_ce1e3b93be1e (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    {j : Fin (N + 1)} (hyj : y j ≠ 0) (pp : Ideal (Poly k N)) [pp.IsPrime]
    (hle : primeOf (S := k) y ≤ pp) (hX : (X j : Poly k N) ∉ pp) {K'' : Type w} [Field K'']
    [Algebra k K''] (ψ : chartRing k y (singleChart hyj) →ₐ[k] K'')
    (hker : RingHom.ker ψ = chartPrime pp hyj) :
    RingHom.ker (ψ.comp (redHom hsp hxy hyj)) = chartPrime pp (hxy j hyj) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrLenRestrict».«ker_comp_redHom» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_ker_comp_redHom_ce1e3b93be1e
