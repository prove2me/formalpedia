-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_ExistsOrthogonalBasisWithUnitNorms_exists_ortho_unit
-- name    : UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_ortho_unit
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:33:54.943182+00:00
-- url     : https://prove2.me/theorems/4f82a9ac-24e5-5cd8-9d7e-883c9b7f1524
-- title:
--   Exists Orthogonal Basis With Unit Norms: exists ortho unit
-- statement:
--   The Exists Orthogonal Basis With Unit Norms construction uses the exists ortho unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsOrthogonalUnitVector.lean#L96-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsOrthogonalUnitVector.lean#L96-L140

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormOneOfPair
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsOrthogonalUnitVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_ortho_unit :
    ∀ {K V : Type} [inst : Field K] [inst_1 : StarRing K] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module K V]
      {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} [FiniteDimensional K V],
      Formalism.HermitianLattices.Ext.L3.WA.IsHermSemilocal S →
        h.IsSymm →
          h.Nondegenerate →
            UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.PairUnit S h →
              ∀ {L : AddSubgroup V},
                Formalism.HermitianLattices.Ext.L3.WA.IsSelfDualMod S h L →
                  ∃ (x : Fin (Module.finrank K V) → V),
                    (∀ (i : Fin (Module.finrank K V)), x i ∈ L) ∧
                      (∀ (i j : Fin (Module.finrank K V)), i ≠ j → ((h : V → V →ₗ[K] K) (x i) : V → K) (x j) = (0 : K)) ∧
                        ∀ (i : Fin (Module.finrank K V)),
                          Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S (((h : V → V →ₗ[K] K) (x i) : V → K) (x i)) := by sorry
