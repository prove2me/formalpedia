-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_main_algebraic_structure
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.main_algebraic_structure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:31:10.210997+00:00
-- url     : https://prove2.me/theorems/f581b5ce-eda1-47e0-a9e3-93771c741287
-- title:
--   Paper main result: algebraic structure of perfectly preserved information
-- statement:
--   Let $\mathcal E$ be a CPTP map between finite-dimensional nonzero complex Hilbert spaces, and let $C$ be a convex set of positive matrices of ordinary trace one. Preservation means equality of $\|\mathcal E(p\rho-(1-p)\sigma)\|_1$ and $\|p\rho-(1-p)\sigma\|_1$ for every $\rho,\sigma\in C$ and $p\in[0,1]$. Maximum means that no code satisfying the same criterion has a proper subset 1-isometric to $C$. A 1-isometry is a complex-linear identification of the code spans that maps the normalized state sets bijectively and preserves every weighted trace-norm distance. If $C$ is maximum preserved, there are a single CPTP recovery $\mathcal R$ and a concrete algebra $A=\bigoplus_k M_{a_k}\otimes I_{b_k}$ on an input support corner such that
--
--   $$\mathcal R\mathcal E(\rho)=\rho\quad(\rho\in C),\qquad C\simeq_1 A_+,\quad A_+=\{X\in A:X\ge0,\operatorname{Tr}X=1\}.$$
--
--   This identifies the full information shape while retaining the operational preservation criterion.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 1, Paper main result: algebraic structure of perfectly preserved information

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

/-- PDF p.1, abstract, pinned to Theorems 4–5 and Corollary 7 (pp.8–10,25).
Maximum codes have an entire algebraic state shape and one exact recovery.
Proper preserved subcodes need only embed in that state shape. -/
theorem main_algebraic_structure {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (E : Superop I J) (hE : IsChannel E) (C : Set (Op I))
    (hC : MaximumCode (Preserved E) C) :
    ∃ R : Superop J I, IsChannel R ∧ (∀ rho ∈ C, R (E rho) = rho) ∧
      ∃ B : BlockModel I, OneIsometric C (statePart B.algebra) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
