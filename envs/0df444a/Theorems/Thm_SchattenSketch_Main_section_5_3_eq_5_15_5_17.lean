-- Prove2me | Theorems.Thm_SchattenSketch_Main_section_5_3_eq_5_15_5_17
-- name    : SchattenSketch.Main.section_5_3_eq_5_15_5_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:57:47.106814+00:00
-- url     : https://prove2.me/theorems/e8ed052b-ab08-4ed2-babc-567df09aefb6
-- title:
--   §5.3, (5.15) and (5.17) — on the covariance event, the head chosen from $GA$ leaves a residual within $6\alpha\|A\|_{S_1}$ of the optimal tail
-- statement:
--   Let $h\ge 1$ and $0<\alpha<1/10$, set $c_0=1$, $\beta_h=c_0\alpha^4/h$ and $F_h=F_h(A)$, and let $A\in\mathbb R^{n\times n}$ and $G\in\mathbb R^{s\times n}$ satisfy the covariance event (5.5),
--   $$(1-\alpha)A^\top A-\beta_hF_h^2I\ \preceq\ A^\top G^\top GA\ \preceq\ (1+\alpha)A^\top A+\beta_hF_h^2I .$$
--   Let $Q_h\in\mathbb R^{n\times h}$ contain the top $h$ right singular vectors of $GA$, $P_h=Q_hQ_h^\top$ and $C_h=A(I-P_h)$. Then
--   $$\|A(I-P_h)\|_{S_1}\le T_h(A)+6\alpha\|A\|_{S_1}\quad(5.15),\qquad 0\le\|AP_h\|_{S_1}+\|C_h\|_{S_1}-\|A\|_{S_1}\le 6\alpha\|A\|_{S_1}\quad(5.17).$$
--
--   The head found from the row sketch leaves almost the same tail mass as the exact singular-value cutoff, with an error relative to the total nuclear norm, and the nuclear norm is approximately additive over head and residual.
--
--   **Formalization Note.** $\preceq$ is the Loewner order (`PosSemidef` of the difference). "$Q_h$ contains the top $h$ right singular vectors of $GA$" is encoded as $Q_h^\top Q_h=I_h$ and $\|GAQ_h\|_F^2=\sum_{i\le h}\sigma_i(GA)^2$: by Ky Fan's maximum principle these are exactly the orthonormal bases of top-$h$ right singular subspaces, ties and rank deficiency included, and the conclusion is asserted for every such choice.
--
--   Differences from the source:
--   - reading: on the event (5.5) of §5.2 with c_0 = 1, β_h = c_0α⁴/h, 0 < α < 1/10, h ≥ 1 → deterministic hypotheses: the two Loewner inequalities of (5.5) for the given A, G; reason: (5.15) and (5.17) are derived from (5.5) alone (pp. 26–27)
--   - encoding: Q_h ∈ R^{n×h} contains the top h right singular vectors of GA → Q_hᵀQ_h = I_h and frobNorm(G A Q_h)² = Σ_{i<h} singVal i (GA)²; reason: Ky Fan's maximum principle: exactly the orthonormal bases of top-h right singular subspaces, ties included
--   - encoding: ⪯ (Loewner order) → Matrix.PosSemidef of the difference; reason: definition
--   - encoding: singular values σ_1 ≥ … ≥ σ_n of A, ‖A‖_{S₁} = Σ σ_i(A) → published singVal (0-based: σ_i = singVal (i - 1)) and nucNorm = Σ_{j<n} singVal j A; reason: Lean indexing; same quantities
-- source:
--   Lin F. Yang, Near-Optimal Bounds for Sketching the Schatten Norms, arXiv:2608.22247 (held version, sha256 c29a210a…), pp. 26–27, §5.3, (5.15) and (5.17) (hypotheses p. 25, (5.4)–(5.5), and p. 26)

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_singVal
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_SchattenSketch_Main_Spectral

open WainwrightHDS.NucNorm

namespace SchattenSketch.Main

/-- §5.3, (5.15) and (5.17) (Yang, pp. 26–27). Let `h ≥ 1`, `0 < α < 1/10`, `A ∈ ℝ^{n×n}` and
`G ∈ ℝ^{s×n}` satisfy the covariance event (5.5) with `c₀ = 1`, `β_h = α⁴/h` and `F_h = F_h(A)`:
`(1 - α) AᵀA - β_h F_h² I ⪯ AᵀGᵀGA ⪯ (1 + α) AᵀA + β_h F_h² I` (Loewner order). Let `Q_h ∈ ℝ^{n×h}`
have orthonormal columns spanning a top-`h` right singular subspace of `GA`, i.e.
`Q_hᵀQ_h = I_h` and `‖GAQ_h‖_F² = ∑_{i ≤ h} σᵢ(GA)²`, `P_h = Q_hQ_hᵀ` and `C_h = A(I - P_h)`.
Then `‖A(I - P_h)‖_{S₁} ≤ T_h(A) + 6α‖A‖_{S₁}` (5.15) and
`0 ≤ ‖AP_h‖_{S₁} + ‖C_h‖_{S₁} - ‖A‖_{S₁} ≤ 6α‖A‖_{S₁}` (5.17). -/
theorem section_5_3_eq_5_15_5_17 (n s h : ℕ) (hh : 1 ≤ h) (α : ℝ) (hα : 0 < α)
    (hα1 : α < 1 / 10) (A : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin s) (Fin n) ℝ)
    (h55lo : (A.transpose * G.transpose * G * A -
        ((1 - α) • (A.transpose * A) - (α ^ 4 / h * tailFrobSq h A) • (1 : Matrix (Fin n) (Fin n) ℝ))).PosSemidef)
    (h55hi : (((1 + α) • (A.transpose * A) + (α ^ 4 / h * tailFrobSq h A) • (1 : Matrix (Fin n) (Fin n) ℝ)) -
        A.transpose * G.transpose * G * A).PosSemidef)
    (Q : Matrix (Fin n) (Fin h) ℝ) (hQ : Q.transpose * Q = 1)
    (hQtop : frobNorm (G * A * Q) ^ 2 = ∑ i ∈ Finset.range h, singVal i (G * A) ^ 2) :
    nucNorm (A * (1 - Q * Q.transpose)) ≤ tailNuc h A + 6 * α * nucNorm A ∧
      0 ≤ nucNorm (A * (Q * Q.transpose)) + nucNorm (A * (1 - Q * Q.transpose)) - nucNorm A ∧
      nucNorm (A * (Q * Q.transpose)) + nucNorm (A * (1 - Q * Q.transpose)) - nucNorm A ≤
        6 * α * nucNorm A := by sorry

end SchattenSketch.Main
