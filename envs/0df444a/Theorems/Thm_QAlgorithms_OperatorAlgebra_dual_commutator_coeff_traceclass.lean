-- Prove2me | Theorems.Thm_QAlgorithms_OperatorAlgebra_dual_commutator_coeff_traceclass
-- name    : QAlgorithms.OperatorAlgebra.dual_commutator_coeff_traceclass
-- status  : Proved
-- author  : @Imine
-- created : 2026-10-21T06:00:23.114895+00:00
-- url     : https://prove2.me/theorems/812d6d79-a34c-4f76-9026-2093069c47df
-- title:
--   Dual-channel commutator matrix coefficients have trace-class representatives
-- statement:
--   Let $\Phi$ be a channel with a genuine trace-class predual and full bounded-observable dual $F$. For every bounded input observable $A$ and every pair $i,j$ of canonical basis indices, there exists an output trace-class operator $Y$ such that
--   $$
--   [F(B)A-AF(B)]_{ij}=\operatorname{Tr}(YB)\qquad\text{for every bounded output observable }B.
--   $$
--   No Weyl, Gaussian, commutation, finite-dimensional, or positivity assumption on the test operator is imposed. This represents the normal functional defined by a commutator matrix coefficient and allows trace-separating observable families to test channel commutation.
--
--   **Formalization Note.** The statement uses the frozen full trace-class duality interface and the canonical matrix coefficients on $\ell^2$.
-- source:
--   Derived trace-duality supporting lemma for Holevo arXiv:1211.4774v1 PDF pp.2–3 (channel duality), p.5 criterion (14). Explicit finite-nuclear construction from the frozen DualChannel pairing; no additional source theorem is silently assumed.

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P18
noncomputable section
set_option autoImplicit false
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Claimed50.P35 (ScaledWeylRepresentation InterleavedPhase tracePair)
open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)
open QAlgorithms.Papers.Independent.Next46.P18 (DualChannel IsCQ)
attribute [local instance] Classical.propDecidable Classical.decEq

theorem QAlgorithms.OperatorAlgebra.dual_commutator_coeff_traceclass
    {I J : Type} (Phi : DualChannel I J)
    (A : Hilbert I →L[ℂ] Hilbert I) (i j : I) :
    ∃ Y : Matrix J J ℂ, IsTraceClass Y ∧ ∀ B : Hilbert J →L[ℂ] Hilbert J,
      operatorCoeff ((Phi.dual B).comp A - A.comp (Phi.dual B)) i j =
        tracePair Y (operatorCoeff B) := by sorry
