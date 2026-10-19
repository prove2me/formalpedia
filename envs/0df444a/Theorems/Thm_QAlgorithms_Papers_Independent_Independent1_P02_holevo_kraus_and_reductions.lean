-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P02_holevo_kraus_and_reductions
-- name    : QAlgorithms.Papers.Independent.Independent1.P02.holevo_kraus_and_reductions
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:16:54.043998+00:00
-- url     : https://prove2.me/theorems/6ffc8b6c-cb86-43cc-aa38-fe1cdeefcea6
-- title:
--   Eq.(3): explicit Kraus representation and CQ/QC reductions
-- statement:
--   Let $d\ge1$, let $\{R_k\}_{k=1}^m$ be density matrices, and let $F_k$ be positive semidefinite. For arbitrary orthonormal bases $\{e_a\}$ and $\{f_b\}$, set $A_{kab}=\sqrt{R_k}|e_a\rangle\langle f_b|\sqrt{F_k}$. Then, on every operator $X$,
--
--   $$\sum_{k,a,b}A_{kab}XA_{kab}^\dagger=\sum_k\operatorname{Tr}(F_kX)R_k.$$
--
--   If the effects form a POVM the Kraus family is normalized. In the CQ case $F_k=|f_k\rangle\langle f_k|$, the reduced family is $\sqrt{R_k}|e_a\rangle\langle f_k|$, and is normalized. In the QC case $R_k=|e_k\rangle\langle e_k|$, it is $|e_k\rangle\langle f_b|\sqrt{F_k}$, normalized when $F$ is a POVM. For pure-output CQ maps it further reduces to $|\psi_k\rangle\langle e_k|$, with unit $\psi_k$.
--
--   These are explicit operator-sum witnesses; square roots are the positive matrix square roots.
-- source:
--   General Entanglement Breaking Channels, arXiv:quant-ph/0302031v2, Eq.(3): explicit Kraus representation and CQ/QC reductions, PDF p. 3. https://arxiv.org/abs/quant-ph/0302031v2 . PDF SHA-256: b9741af8740a74b5771c71520597f0a6ee2fa27a7ab56de59ddd399c4f49c465.

import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
set_option autoImplicit false

/-!
# Entanglement Breaking Channels (quant-ph/0302031v2)

All reference factors occur first. General EB uses the separable positive cone;
EBT additionally preserves trace. Proposed source corrections below require
independent source moderation; see MODERATION_NOTES.md in the assigned unit.
-/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P02






















































/-- Eq.(3), PDF p.3 and reductions p.4, with arbitrary orthonormal bases.
POVM hypotheses are needed only for the corresponding Kraus normalization. -/
theorem holevo_kraus_and_reductions (d : ℕ) (hd : 0 < d) :
    (∀ (m : ℕ) (R F : Fin m → Algebra d), (∀ k, IsDensityMatrix (R k)) →
      (∀ k, (F k).PosSemidef) →
      ∀ e f : OrthonormalBasis (Fin d) ℂ (StateVector d),
      (∀ X, krausApply (holevoKrausOperators R F e f) X = Entanglement.holevoMap R F X) ∧
      (IsPOVM F → IsKrausFamily (holevoKrausOperators R F e f))) ∧
    (∀ R : Fin d → Algebra d, (∀ k, IsDensityMatrix (R k)) →
      ∀ e f : OrthonormalBasis (Fin d) ℂ (StateVector d),
      (∀ X, krausApply (cqKrausOperators R e f) X =
        Entanglement.holevoMap R (fun k => pureDensity (f k)) X) ∧
      IsKrausFamily (cqKrausOperators R e f)) ∧
    (∀ F : Fin d → Algebra d, (∀ k, (F k).PosSemidef) →
      ∀ e f : OrthonormalBasis (Fin d) ℂ (StateVector d),
      (∀ X, krausApply (qcKrausOperators F e f) X =
        Entanglement.holevoMap (fun k => pureDensity (e k)) F X) ∧
      (IsPOVM F → IsKrausFamily (qcKrausOperators F e f))) ∧
    (∀ (e : OrthonormalBasis (Fin d) ℂ (StateVector d)) (psi : Fin d → StateVector d),
      (∀ k, IsState (psi k)) →
      (∀ X, krausApply (fun k => outerOperator (psi k) (e k)) X = pureCQEndomorphism e psi X) ∧
      IsKrausFamily (fun k => outerOperator (psi k) (e k))) := by sorry















end QAlgorithms.Papers.Independent.Independent1.P02
