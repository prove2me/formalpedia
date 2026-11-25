-- Prove2me | Theorems.Thm_P2M_GlobalTheory_formallyEtale_mvPolynomial_eval__tensor_865e95252550
-- name    : P2M_GlobalTheory_formallyEtale_mvPolynomial_eval__tensor_865e95252550
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:12:12.872503+00:00
-- url     : https://prove2.me/theorems/745736b1-4c66-4cdf-830b-819aa1373453
-- title:
--   P2 M Global Theory formally Etale mv Polynomial eval  tensor 865e95252550: P2 M Global Theory formally Etale mv Polynomial eval  tensor 865e95252550
-- statement:
--   The P2 M Global Theory formally Etale mv Polynomial eval  tensor 865e95252550 construction uses the P2 M Global Theory formally Etale mv Polynomial eval  tensor 865e95252550 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FormallyEtaleBaseChangeEvalHom.lean#L8-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FormallyEtaleBaseChangeEvalHom.lean#L8-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FormallyEtaleBaseChangeEvalHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem P2M_GlobalTheory_formallyEtale_mvPolynomial_eval__tensor_865e95252550 {k R B : Type} [CommRing k] [CommRing R]
    [CommRing B] [Algebra k R] [Algebra k B] {r : ℕ} (τ : Fin r → B)
    (hf : (MvPolynomial.eval₂Hom (algebraMap k B) τ).FormallyEtale) :
    (MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] B)
      (fun i => (1 : R) ⊗ₜ[k] τ i)).FormallyEtale := by sorry

alias «GlobalTheory».«formallyEtale_mvPolynomial_eval₂_tensor» := P2M_GlobalTheory_formallyEtale_mvPolynomial_eval__tensor_865e95252550
