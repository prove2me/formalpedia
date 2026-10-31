-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P54_placedConfigurations_chambers
-- name    : QAlgorithms.Papers.Independent.Intake100.P54.placedConfigurations_chambers
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:48:26.5242+00:00
-- url     : https://prove2.me/theorems/9e9aa3b2-a81d-49ac-8e71-322e6d8bcff1
-- title:
--   §5.10: placed configurations and their tableau correspondence
-- statement:
--   Let $\gamma=(\gamma_1\le\cdots\le\gamma_n)\in\mathbb Z^n$, and write $Z=\{\alpha>0:\langle\gamma,\alpha\rangle=0\}$ and $P=\{\alpha>0:\langle\gamma,\alpha\rangle=1\}$ for the type $A_{n-1}$ positive roots $\varepsilon_j-\varepsilon_i$, $i<j$. Suppose $J\subseteq P$ satisfies
--
--   $$\beta\in J,\quad\alpha\in Z,\quad\beta-\alpha\in R^+\quad\Longrightarrow\quad\beta-\alpha\in J.$$
--
--   There is a configuration of $n$ disjoint boxes, numbered by diagonal content and northwest-to-southeast order on each diagonal, whose contents are $\gamma_i$. For adjacent diagonals, box $b_j$ is northwest of $b_i$ exactly when $\varepsilon_j-\varepsilon_i\in J$, and otherwise is southeast. The configuration is determined up to diagonal slides preserving orders on the same and adjacent diagonals. Its standard fillings are bijective fillings by $1,\ldots,n$ satisfying the same-diagonal and adjacent-diagonal inequalities in §5.10. The word map is a bijection
--
--   $$\{\text{standard configuration fillings}\}\ \longrightarrow\ F^{(\gamma,J)},\qquad p\longmapsto(p(b_1),\ldots,p(b_n)),$$
--
--   where $F^{(\gamma,J)}=\{w\in S_n:R(w)\cap Z=\varnothing,\ R(w)\cap P=J\}$. This extends the skew-tableau correspondence to configurations that need not be skew diagrams.
-- source:
--   Affine Hecke algebras and generalized standard Young tableaux, arXiv:math/0401329v2, PDF p. 25, §5.10

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P54

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P54

/-- §5.10, PDF pp.25–26: the closure condition produces a configuration,
unique up to preserved diagonal/adjacent-diagonal orders, and its geometric
standard fillings correspond by the word map to F(gamma,J). The source's
reference to Theorem 5.6 here means Theorem 5.9. -/
theorem placedConfigurations_chambers {n : ℕ} (gamma : Fin n → ℤ)
    (hgamma : Monotone gamma) (J : Set (ARoot n))
    (hJ : J ⊆ aUnitRoots (fun i => (gamma i : ℝ)))
    (hclosed : aConfigurationClosure (fun i => (gamma i : ℝ)) J) :
    ∃ D : BoxDrawing n, ConfigurationFor gamma J D ∧
      (∀ E : BoxDrawing n, ConfigurationFor gamma J E → SlideEquivalent D E) ∧
      (∃ e : ConfigurationTableaux D ≃
        {w : Equiv.Perm (Fin n) // w ∈ aRegion (fun i => (gamma i : ℝ)) J},
        ∀ p : ConfigurationTableaux D, (e p).val = tableauWord p.val) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P54

end
