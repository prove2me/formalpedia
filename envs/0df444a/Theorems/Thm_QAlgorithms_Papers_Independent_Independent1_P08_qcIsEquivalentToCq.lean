-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_qcIsEquivalentToCq
-- name    : QAlgorithms.Papers.Independent.Independent1.P08.qcIsEquivalentToCq
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:15:49.058801+00:00
-- url     : https://prove2.me/theorems/9eee9e7e-809f-430a-a1aa-579ec2bb6389
-- title:
--   QC channels are unitarily equivalent to CQ channels
-- statement:
--   Let $\Phi$ be a QC qubit channel: it measures a POVM and prepares one of two orthogonal pure states. There are qubit unitaries $U,V$ and a CQ map $\Psi$ such that
--
--   $$\Phi=\operatorname{Ad}_V\circ\Psi\circ\operatorname{Ad}_U,\qquad \operatorname{Ad}_U(X)=UXU^\dagger.$$
--
--   A CQ map measures rank-one orthogonal input projectors and prepares density matrices. The assertion relates these two channel subclasses without identifying their definitions.
-- source:
--   Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3, QC channels are unitarily equivalent to CQ channels, PDF p. 6. https://arxiv.org/abs/quant-ph/0302032v3 . PDF SHA-256: dba60bd30b3ca1e23dac55f1e413d595e822e7d75c0dff71bf1b94f65337b81d.

import Definitions.Def_QAlgorithms_Defs_QubitBlochMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P08_Model
set_option autoImplicit false

/-! Ruskai, Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3.
All locators are PDF pages. Convexity is real; ambiguous claims are in HARD.md. -/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P08

open QAlgorithms.Entanglement QAlgorithms.QubitChannels






































































/-- QC to CQ, PDF pp.6-7, with independent unitary bases. -/
theorem qcIsEquivalentToCq (Phi : QMap) (hPhi : IsQC Phi) :
    ∃ U V : Matrix.unitaryGroup Bool ℂ, ∃ Psi : QMap,
      IsCQMap Psi ∧ Phi = changeBases U V Psi := by sorry















end QAlgorithms.Papers.Independent.Independent1.P08
