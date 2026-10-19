-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_exceptionalKernelStructure
-- name    : QAlgorithms.Papers.Independent.Information100.P22.exceptionalKernelStructure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:03:16.708979+00:00
-- url     : https://prove2.me/theorems/30d1f5f5-f1c3-44cf-aa26-6fb770acee92
-- title:
--   Lemma S4: Exceptional kernel structure
-- statement:
--   For $m\ge2$, $k\ge1$ and a fixed graph cut, let $x\in\ker B^T$. Define exceptionality operationally by the support of $U(I_A\otimes K_S(x))U^\dagger$ being contained in $A$. Then
--   $$x\text{ exceptional}\iff x\in E_{P,Q}^{(m,k)}(A_S),$$
--   where the ambient space is zero for even $m$ and odd XY/YX; for odd XZ/ZX it consists of $Fc$ with $(A_S+I)Fc=0$ and $\sum_jc_j=0$; for odd YZ/ZY it consists of $Fc$ with $A_SFc=0$. This reconciles support exceptionality with the explicit binary equations.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 30, Lemma S4: Exceptional kernel structure

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Lemma S4, PDF pp.30–31: support definition matches the ambient binary conditions on K. -/
theorem exceptionalKernelStructure (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (P Q : Axis) (hPQ : P ≠ Q) (G : CutGraph (Wires m k))
    (x : Wires m k → F2) (hx : x ∈ cutKernel G) :
    ExceptionalVector P Q G x ↔ x ∈ exceptionalSpace P Q G.AS := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
