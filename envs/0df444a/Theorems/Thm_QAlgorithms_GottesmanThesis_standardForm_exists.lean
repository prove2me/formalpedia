-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanThesis_standardForm_exists
-- name    : QAlgorithms.GottesmanThesis.standardForm_exists
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:59:29.383015+00:00
-- url     : https://prove2.me/theorems/55d5712e-4688-4e40-aff3-ac3f89d5b76e
-- title:
--   Every stabilizer code can be put into the standard form (4.3)
-- statement:
--   Consider a stabilizer code on $n=m+k$ qubits encoding $k$ qubits, described in the binary language: its $m=n-k$ generators $M_1,\dots,M_m$ are the rows of the $m\times 2n$ matrix $(H_x\,|\,H_z)$ over $\mathbb F_2$, where $H_x$ records the $\sigma_x$ parts and $H_z$ the $\sigma_z$ parts (a $\sigma_y$ factor contributes $(1|1)$). Assume the generators commute, i.e. $H_xH_z^{\mathsf T}+H_zH_x^{\mathsf T}=0$, and are independent, i.e. the rows of $(H_x\,|\,H_z)$ are linearly independent over $\mathbb F_2$. Let $r=\operatorname{rank}H_x$.
--
--   Then there exist an invertible matrix $G\in GL_m(\mathbb F_2)$ (a sequence of generator replacements $M_i\mapsto M_iM_j$) and a permutation $\sigma$ of the $n$ qubits (applied to the columns of both halves) such that $(GH_xP_\sigma\,|\,GH_zP_\sigma)$ is in the standard form
--   $$\left(\begin{array}{ccc|ccc} I & A_1 & A_2 & B & C_1 & C_2\\ 0 & 0 & 0 & D & I & E\end{array}\right),$$
--   where the row blocks have heights $r$ and $n-k-r$, and the column blocks in each half have widths $r$, $n-k-r$ and $k$; the blocks $A_1,A_2,B,C_1,C_2,D,E$ are arbitrary.
--
--   The standard form is the starting point for the construction of the logical operators and of the encoding network in Gottesman's thesis.
--
--   **Formalization Note** Row operations are modelled by an arbitrary invertible $G$ (row additions generate $GL_m(\mathbb F_2)$), and the qubit rearrangement by `Matrix.submatrix id σ`, so the reachable set is exactly the page's. The rank parameter is the rank of the original $H_x$, which equals that of the transformed one.
-- source:
--   Daniel Gottesman, Stabilizer Codes and Quantum Error Correction, 1997 thesis, downloaded arXiv v1 PDF; PDF title page now prints 2024, PDF p. 39, §4.1. https://arxiv.org/pdf/quant-ph/9705052v1

import Definitions.Def_QAlgorithms_Defs_BinaryStabilizer
set_option autoImplicit false

namespace QAlgorithms.GottesmanThesis

/-- Gottesman thesis p.39, §4.1 (unnumbered; equations (4.1)–(4.3)): every stabilizer code can
be put into the standard form (4.3). Let `(H_x | H_z)` be the binary generator matrix of `m`
independent commuting generators on `m + k` qubits (rows commute symplectically, eq. (3.23);
rows linearly independent over `F₂`). Then some sequence of generator replacements
`M_i ↦ M_i M_j` (row additions in both halves, i.e. left multiplication by an invertible
`G ∈ GL_m(F₂)`) and some rearrangement of the qubits (the same column permutation `σ` in both
halves) brings it to the standard form (4.3) with `r = rank H_x`: the first `r` rows read
`I A₁ A₂ | B C₁ C₂`, the last `m − r` rows read `0 0 0 | D I E`. -/
theorem standardForm_exists {m k : ℕ} (Hx Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2))
    (hS : IsBinaryStabilizerMatrix Hx Hz) :
    ∃ G : Matrix.GeneralLinearGroup (Fin m) (ZMod 2), ∃ σ : Equiv.Perm (Fin (m + k)),
      IsStandardForm Hx.rank ((G : Matrix (Fin m) (Fin m) (ZMod 2)) * Hx.submatrix id σ)
        ((G : Matrix (Fin m) (Fin m) (ZMod 2)) * Hz.submatrix id σ) := by
  sorry


end QAlgorithms.GottesmanThesis
