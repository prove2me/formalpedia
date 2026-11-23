-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Yzd4_lcsc_HA
-- name    : UpperTheory.Reformulated.B.Yzd4.lcsc_HA
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:44.149804+00:00
-- url     : https://prove2.me/theorems/60a2f3c9-4efb-4a4a-b56e-7de6e25cc60a
-- title:
--   Yzd4: lcsc HA
-- statement:
--   The Yzd4 construction uses the lcsc HA property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ConjInvariantCharacterMem.lean#L1712-L1756
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ConjInvariantCharacterMem.lean#L1712-L1756

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ConjInvariantCharacterMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
attribute [local instance] UpperTheory.Reformulated.B.Yzd4.instTopologicalSpaceHA

theorem UpperTheory.Reformulated.B.Yzd4.lcsc_HA :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
      [inst_2 :
        @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))]
      [@FiniteDimensional F E (@Field.toDivisionRing F inst)
          (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_1)))
          (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2)]
      (R : Type) [inst_4 : CommRing R]
      [inst_5 :
        @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_4))]
      [inst_6 : TopologicalSpace R]
      [@IsTopologicalRing R inst_6
          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing R
            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing R (@CommRing.toNonUnitalCommRing R inst_4)))]
      [@LocallyCompactSpace R inst_6] [@SecondCountableTopology R inst_6] [@T2Space R inst_6]
      (σ :
        @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2 inst_2)
      (M : Nat) (J : Matrix (Fin M) (Fin M) E),
      And
        (@LocallyCompactSpace (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J)
          (@UpperTheory.Reformulated.B.Yzd4.instTopologicalSpaceHA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J inst_6))
        (And
          (@SecondCountableTopology (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J)
            (@UpperTheory.Reformulated.B.Yzd4.instTopologicalSpaceHA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J inst_6))
          (@T2Space (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J)
            (@UpperTheory.Reformulated.B.Yzd4.instTopologicalSpaceHA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J inst_6))) := by sorry
