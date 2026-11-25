-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__covolume_trace_lattice_48d268a15504
-- name    : P2M_Formalism_MainNotions_BridgeLemma__covolume_trace_lattice_48d268a15504
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:00:38.391877+00:00
-- url     : https://prove2.me/theorems/a94ec406-0745-48da-a8ce-a5312e6c7685
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  covolume trace lattice 48d268a15504: P2 M Formalism Main Notions Bridge Lemma  covolume trace lattice 48d268a15504
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  covolume trace lattice 48d268a15504 construction uses the P2 M Formalism Main Notions Bridge Lemma  covolume trace lattice 48d268a15504 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/TraceInnerPosOfOrthonormalPair.lean#L147-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/TraceInnerPosOfOrthonormalPair.lean#L147-L220

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_TraceInnerPosOfOrthonormalPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField Module Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem P2M_Formalism_MainNotions_BridgeLemma__covolume_trace_lattice_48d268a15504 (hK : IsCMUnram K) (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Fin 2 → V) (hli : LinearIndependent K e)
    (hsp : Submodule.span K (Set.range e) = ⊤) (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0)
    (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    [DiscreteTopology (zmap ι (Submodule.span (𝓞 K) (Set.range e)))]
    [IsZLattice ℝ (zmap ι (Submodule.span (𝓞 K) (Set.range e)))] :
    ZLattice.covolume (zmap ι (Submodule.span (𝓞 K) (Set.range e))) = |(discr K : ℝ)| ∧ N = 2 * finrank ℚ K := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«covolume_trace_lattice» := P2M_Formalism_MainNotions_BridgeLemma__covolume_trace_lattice_48d268a15504
