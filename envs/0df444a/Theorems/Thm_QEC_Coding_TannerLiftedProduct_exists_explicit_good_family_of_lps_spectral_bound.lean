-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_explicit_good_family_of_lps_spectral_bound
-- name    : QEC.Coding.TannerLiftedProduct.exists_explicit_good_family_of_lps_spectral_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:37:38.91013+00:00
-- url     : https://prove2.me/theorems/80495a7e-3f23-4b89-a988-a1530ff944b6
-- title:
--   Tanner Lifted Product: exists explicit good family of lps spectral bound
-- statement:
--   An explicit good PK22 family and its polynomial-in-physical-length sparse
--   output program, under the external LPS bound on the actual selected graphs.
--   The same field tables, local matrices, program and polynomial serve the whole
--   cofinal family. Decoded output cuts out the carrier of that very family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QLDPC/ConditionalLiftedProductFamily.lean#L35-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QLDPC/ConditionalLiftedProductFamily.lean#L35-L107

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGoodFamilyAssembly
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterFamilyMachine
import Definitions.Def_QEC_Results_QLDPC_ConditionalLiftedProductFamily
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_eq_prime_add_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_608e2928fd_22
attribute [local instance] QEC.Coding.TannerLiftedProduct.pk22ConditionalQubitDecidableEq

theorem QEC.Coding.TannerLiftedProduct.exists_explicit_good_family_of_lps_spectral_bound
    (F : Type) [Field F] [Fintype F]
    (targetRate : ℝ) (hRatePositive : 0 < targetRate) (hRate : targetRate < 1)
    (hLPS : ∀ (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ),
      SmallSetExpansion.HasMeanZeroComplexOperatorBound
        (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 B))
        (2 * Real.sqrt (p : ℝ))) :
    ∃ (t : ℕ)
      (a : CompatibleDegreePrime (pk22LocalWidth (Nat.card F) t))
      (h h' : Matrix (PK22Check (Nat.card F) t a)
        (PK22Direction (Nat.card F) t a) F)
      (e : Fin (Fintype.card F) ≃ F),
      let hCount := card_lpsQuaternionShell_eq_prime_add_one a.prime a.oneModFour
      let family := lpsSemanticFamily a.prime a.oneModFour hCount h h'
      let r := pk22RowCoefficient (Nat.card F) t * a.blocks
      let tables := encodedFieldTables e
      let g := LPSSparseEmitterFamily.sourceDirections a.prime a.oneModFour
      let hc := h.map e.symm
      let hc' := h'.map e.symm
      QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily family ∧
      QEC.QLDPC.HasEventualRateAtLeast family targetRate ∧
      (∀ B : ℕ,
        LPSSparseEmitterFamily.physicalSize
          (lpsEffectiveResiduePrimeAt a.prime a.oneModFour B) (a.p + 1) r r =
            family.blockLength B) ∧
      (∀ B : ℕ, Nonempty (TM2OutputsInTime
        (LPSSparseEmitterFamily.sourceMachine a.prime a.oneModFour tables hc hc').toFinTM2
        (unary B)
        (some (LPSSparseEmitterFamily.sourceOutput a.prime a.oneModFour B tables hc hc'))
        ((LPSSparseEmitterFamily.sourceTime a.prime a.oneModFour tables hc hc').eval
          (family.blockLength B)))) ∧
      (∀ B : ℕ,
        LPSSparseEmitterCodec.decodeTyped
          (LPSSparseEmitterFamily.PhysicalCount
            (lpsEffectiveResiduePrimeAt a.prime a.oneModFour B).q (a.p + 1) r r)
          (Fintype.card F)
          (LPSSparseEmitterFamily.sourceOutput a.prime a.oneModFour B tables hc hc') =
        some (lpsEncodedCheckOutput tables
          (fun j => lpsEffectiveQuaternionFamilyIndex a.prime a.oneModFour B (g j))
          hc hc')) ∧
      (∀ (B : ℕ)
        (ψ : Semantics.Qudit.QuditRegister
          (fun _ : FamilyQubitIndex
            (W := Fin (a.p + 1)) (R := PK22Check (Nat.card F) t a)
            (R' := PK22Check (Nat.card F) t a)
            (G := LPSVertexGroup a.prime a.oneModFour) B => Fintype.card F)),
        ψ ∈ (family.presentation B).code.carrier ↔
          ∀ i : Fin (LPSSparseEmitterFamily.CheckCount
            (lpsEffectiveResiduePrimeAt a.prime a.oneModFour B).q
            (a.p + 1) r r (Fintype.card F)),
          LPSSparseEmitterFamily.decodedOperator e tables i
            (LPSSparseEmitterFamily.sourceOutput a.prime a.oneModFour B tables hc hc') ψ = ψ) := by sorry
