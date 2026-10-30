-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_defectPairRealization
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.defectPairRealization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:12:01.104609+00:00
-- url     : https://prove2.me/theorems/377b09c1-12fa-429f-b4d0-d28fd7bd19b6
-- title:
--   Realizing compatible left and right defects
-- statement:
--   Let $d$ be prime and $t\geq1$. Any two defect subspaces $N,M$ of equal dimension, with $\mathbf1_t\in N$ if and only if $\mathbf1_t\in M$, occur as the left and right kernels of a stochastic Lagrangian relation.
--
--   $$
--   \exists T\in\Sigma_{t,t}(d):\quad T_{LD}=N,\quad T_{RD}=M.
--   $$
--
--   This gives the source's realizing compatible left and right defects in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 38, corollary-4.19

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.38, Corollary 4.19: every compatible pair occurs as actual relation defects. -/
theorem defectPairRealization (d t : ℕ) [NeZero d] [Fact (Nat.Prime d)] (ht : 1 ≤ t)
    (N M : Submodule (ZMod d) (ResidueRegister d t)) (hN : IsDefect N) (hM : IsDefect M)
    (hdim : Module.finrank (ZMod d) N = Module.finrank (ZMod d) M)
    (hone : (fun _ => 1) ∈ N ↔ (fun _ => 1) ∈ M) :
    ∃ T : Lagrangian d t, leftDefect T.val = N ∧ rightDefect T.val = M := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
