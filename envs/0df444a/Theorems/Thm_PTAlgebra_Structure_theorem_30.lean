-- Prove2me | Theorems.Thm_PTAlgebra_Structure_theorem_30
-- name    : PTAlgebra.Structure.theorem_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:31.957833+00:00
-- url     : https://prove2.me/theorems/110464db-d4e3-444a-91bd-008f78482c93
-- title:
--   Theorem 30, pp. 8–9 — full structure of the partially transposed permutation algebra
-- statement:
--   Let $n=m+2\ge2$, $d\ge1$, and let $A=A_n^{t_n}(d)$ be the complex span of all partially transposed permutation operators on $(\mathbb C^d)^{\otimes n}$. Let $M$ be the span of those indexed by permutations moving the last position. For a complete family $\varphi^\alpha$ of irreducible representations of $S(n-2)$, Definition 40 constructs $U(\alpha)$ and Definition 29 constructs $Q(\alpha)$.
--
--   Theorem 30 states that $A=M\oplus S$ for a two-sided ideal $S$ annihilating $M$ on both sides, and
--   $$M=\bigoplus_{\varphi^\alpha\subseteq V_d[S(n-2)]}U(\alpha),\quad U(\alpha)\cong M_{\operatorname{rank}Q(\alpha)}(\mathbb C),\quad S\cong\bigoplus_{\substack{\nu\vdash n-1\\h(\nu)<d}}M_{\dim\psi^\nu}(\mathbb C).$$
--   Each $U(\alpha)$ is a two-sided ideal of $A$. If $\det Q(\alpha)\ne0$, its matrix order is $(n-1)\dim\varphi^\alpha$. Their generators obey $u^{ab}_{ij}(\alpha)u^{pq}_{kl}(\beta)=\delta_{\alpha\beta}Q^{bp}_{jk}(\alpha)u^{aq}_{il}(\alpha)$, with the mixed product zero when the labels differ. The ideals on the $S$ side are independent, span $S$, and have orders $\dim\psi^\nu$.
--
--   This is the paper's classification of the algebra into full matrix ideals, including singular $Q(\alpha)$ and small $d$.
--
--   **Formalization Note** The two cases of part (b) are written uniformly as $h(\nu)<d$. The order $\dim\psi^\nu$ is the standard Young-tableau count. An isomorphism to $M_r(\mathbb C)$ is witnessed by independent matrix units spanning the ideal. The real orthogonal irrep family is required to be complete by $\sum_\alpha(w^\alpha)^2=(n-2)!$. The coefficient $Q^{bp}_{jk}$ follows Proposition 44, equation (6), correcting the index slip in Theorem 30(a).
-- source:
--   Mozrzymas, Horodecki, Studziński, Structure and properties of the algebra of partially transposed permutation operators, arXiv:1308.2653v3, pp. 8–9, Theorem 30

import Mathlib
import Definitions.Def_PTAlgebra_Structure_Defs

namespace PTAlgebra.Structure

open PTCommutant.OperatorBasis
open scoped BigOperators

/-- Theorem 30, pp. 8–9, including the multiplication law of part (a). -/
theorem theorem_30 {m : ℕ} (d : ℕ) (hd : 1 ≤ d) (F : IrrepFamily m)
    (hcomplete : ∑ α : F.ι, (F.dim α) ^ 2 = m.factorial) :
    ∃ S : Submodule ℂ (Op d (m + 2)),
      IsIdealOf (algM d m) (algA d m) ∧ IsIdealOf S (algA d m) ∧
      algM d m ⊓ S = ⊥ ∧ algM d m ⊔ S = algA d m ∧
      (∀ x ∈ algM d m, ∀ y ∈ S, x * y = 0 ∧ y * x = 0) ∧
      (∀ α : {α : F.ι // Occurs d F α},
        IsIdealOf (Uideal d F α.1) (algA d m) ∧
        IsMatrixIdeal (Uideal d F α.1) (Qmat d F α.1).rank ∧
        ((Qmat d F α.1).det ≠ 0 →
          IsMatrixIdeal (Uideal d F α.1) ((m + 1) * F.dim α.1))) ∧
      (∀ (α : F.ι), Occurs d F α →
        ∀ (a b p q : Fin (m + 1)) (i j k l : Fin (F.dim α)),
          uOp d F α a b i j * uOp d F α p q k l =
            (Qmat d F α (b, j) (p, k)) • uOp d F α a q i l) ∧
      (∀ (α β : F.ι), Occurs d F α → α ≠ β →
        ∀ (a b p q : Fin (m + 1)) (i j : Fin (F.dim α))
          (k l : Fin (F.dim β)),
          uOp d F α a b i j * uOp d F β p q k l = 0) ∧
      iSupIndep (fun α : {α : F.ι // Occurs d F α} => Uideal d F α.1) ∧
      (⨆ α : {α : F.ι // Occurs d F α}, Uideal d F α.1) = algM d m ∧
      ∃ T : {ν : Nat.Partition (m + 1) // hgt ν < d} →
          Submodule ℂ (Op d (m + 2)),
        (∀ ν, IsIdealOf (T ν) (algA d m) ∧ IsMatrixIdeal (T ν) (numSYT ν.1)) ∧
        iSupIndep T ∧ (⨆ ν, T ν) = S := by sorry

end PTAlgebra.Structure
