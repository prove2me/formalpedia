-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_proposition1_exact_recovery
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.proposition1_exact_recovery
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:32:06.257342+00:00
-- url     : https://prove2.me/theorems/b1ff86b8-99c9-4c2f-8646-f903121b3bfb
-- title:
--   Proposition 1: maximum isometric codes admit exact recovery
-- statement:
--   Let $\mathcal E$ be a CPTP map between finite-dimensional nonzero complex Hilbert spaces, and let $C$ be a convex set of positive matrices of ordinary trace one. Preservation means equality of $\|\mathcal E(p\rho-(1-p)\sigma)\|_1$ and $\|p\rho-(1-p)\sigma\|_1$ for every $\rho,\sigma\in C$ and $p\in[0,1]$. Maximum means that no code satisfying the same criterion has a proper subset 1-isometric to $C$. For every maximum preserved $C$, there is one CPTP map $\mathcal R$ back to the input space with
--
--   $$\forall\rho\in C,\quad\mathcal R(\mathcal E(\rho))=\rho.$$
--
--   This gives exact correction of the entire code. Proposition 1 and Corollary 7 are the announced and proved versions of the same assertion.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 7, Proposition 1: maximum isometric codes admit exact recovery

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P70

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P70

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

/-- PDF p.7, Proposition 1; proved again as Corollary 7, pp.10,26.
The single recovery is chosen before every code state. -/
theorem proposition1_exact_recovery {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (E : Superop I J) (hE : IsChannel E) (C : Set (Op I))
    (hC : MaximumCode (Preserved E) C) :
    ∃ R : Superop J I, IsChannel R ∧ ∀ rho ∈ C, R (E rho) = rho := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
