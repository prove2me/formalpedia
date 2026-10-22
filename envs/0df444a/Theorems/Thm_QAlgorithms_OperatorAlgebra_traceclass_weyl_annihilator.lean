-- Prove2me | Theorems.Thm_QAlgorithms_OperatorAlgebra_traceclass_weyl_annihilator
-- name    : QAlgorithms.OperatorAlgebra.traceclass_weyl_annihilator
-- status  : Proved
-- author  : @Imine
-- created : 2026-10-21T06:00:08.808302+00:00
-- url     : https://prove2.me/theorems/8c618d2f-c607-4d0a-859f-05539c996bae
-- title:
--   Trace-class Weyl characteristic functions separate operators
-- statement:
--   Let $W$ be a regular irreducible finite-mode Weyl representation on the separable Hilbert space $\ell^2(J)$, with Planck constant one. Let $X$ be any trace-class operator; positivity and self-adjointness are not required. Then
--   $$
--   \bigl[\operatorname{Tr}(XW(z))=0\ \text{for every }z\in\mathbb R^{2t}\bigr]\quad\Longrightarrow\quad X=0.
--   $$
--   This is a completeness statement for Weyl observables, independent of channels or commutation of their images. The zero-mode case is included. It supplies the analytic testing step in extending a channel identity from Weyl observables to all bounded observables.
--
--   **Formalization Note.** The operator is represented by the frozen nuclear coefficient-array interface. This supporting analytic theorem remains open; no density assumption has been added to the original channel theorem.
-- source:
--   Supporting analytic lemma for Holevo, Gaussian classical-quantum channels: gain of entanglement-assistance, arXiv:1211.4774v1, PDF p.5, criterion (14). The paper states the CQ criterion; the ultraweak-density/injectivity justification is a separate analytic foundation, not a proof claimed to appear verbatim in that source.

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P18
noncomputable section
set_option autoImplicit false
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Claimed50.P35 (ScaledWeylRepresentation InterleavedPhase tracePair)
open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)
open QAlgorithms.Papers.Independent.Next46.P18 (DualChannel IsCQ)
attribute [local instance] Classical.propDecidable Classical.decEq

theorem QAlgorithms.OperatorAlgebra.traceclass_weyl_annihilator
    {J : Type} [Countable J] [Nonempty J] {t : ℕ}
    (W : ScaledWeylRepresentation J t 1) (X : Matrix J J ℂ)
    (hX : IsTraceClass X)
    (h : ∀ z : InterleavedPhase t, tracePair X (operatorCoeff (W.operator z)) = 0) :
    X = 0 := by sorry
