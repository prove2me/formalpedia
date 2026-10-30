-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_defectOrbitTransitivity
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.defectOrbitTransitivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:11:00.8002+00:00
-- url     : https://prove2.me/theorems/8e83aef1-9fc9-45c6-b9cb-731e0da0d3cc
-- title:
--   Transitivity on compatible defect subspaces
-- statement:
--   For prime $d$ and $t\geq1$, let $N,M\subseteq\mathbb F_d^t$ be totally quadratic-isotropic, co-stochastic defect subspaces. If they have equal dimension and contain $\mathbf1_t$ simultaneously, a stochastic isometry maps $N$ onto $M$.
--
--   $$
--   \dim N=\dim M,\quad(\mathbf1_t\in N\iff\mathbf1_t\in M)\ \Longrightarrow\ \exists O\in O_t(d):ON=M.
--   $$
--
--   This gives the source's transitivity on compatible defect subspaces in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 38, lemma-4.18

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.38, Lemma 4.18: both defect invariants are needed. -/
theorem defectOrbitTransitivity (d t : ℕ) [NeZero d] [Fact (Nat.Prime d)] (ht : 1 ≤ t)
    (N M : Submodule (ZMod d) (ResidueRegister d t)) (hN : IsDefect N) (hM : IsDefect M)
    (hdim : Module.finrank (ZMod d) N = Module.finrank (ZMod d) M)
    (hone : (fun _ => 1) ∈ N ↔ (fun _ => 1) ∈ M) :
    ∃ O : StochasticOrthogonal d t, (fun x => O.val.mulVec x) '' (N : Set _) = (M : Set _) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
