-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckeFiberEquiv_root
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeFiberEquiv_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:28:19.315939+00:00
-- url     : https://prove2.me/theorems/e279d74c-7114-44bf-82e2-207ab8ad7cbf
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Hecke Fiber Equiv root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Hecke Fiber Equiv root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L171-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L171-L182

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeFiberEquiv_root
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q
      (Ideal.Quotient.mk (q.map (AdjoinRoot.of
        (lpsOriginalRelativeGaussHeckePolynomial N hN p)))
        (AdjoinRoot.root (lpsOriginalRelativeGaussHeckePolynomial N hN p))) =
      ((lpsOriginalGaussMaximalResidueJN N hN p q)^p,
        AdjoinRoot.root ((Polynomial.X : Polynomial
          (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
            Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))) := by sorry
