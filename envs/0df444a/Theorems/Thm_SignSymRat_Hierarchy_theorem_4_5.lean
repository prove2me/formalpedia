-- Prove2me | Theorems.Thm_SignSymRat_Hierarchy_theorem_4_5
-- name    : SignSymRat.Hierarchy.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:08:28.747227+00:00
-- url     : https://prove2.me/theorems/49913e4d-1860-4197-a147-65464f19f457
-- title:
--   Theorem 4.5 — sign-symmetric Positivstellensatz
-- statement:
--   Let $g_1,\ldots,g_m$ define $K=\{x:g_j(x)\ge0\}$, and let $f$ be a real polynomial. Form $A=\operatorname{supp}(f)\cup\bigcup_j\operatorname{supp}(g_j)$. If the ordinary quadratic module $Q(g)$ is Archimedean and $f$ is strictly positive on $K$, then
--
--   $$\exists k\in\mathbb N,\qquad f\in Q_k(g,A).$$
--
--   The result provides sparse SOS certificates for positive polynomials with the source's support-dependent pattern. It is cited in the paper from Wang, Magron and Lasserre.
--
--   **Formalization Note** The sparse module uses PSD Gram matrices with zero entries when $\alpha+\beta\notin\bar A$. The Archimedean condition concerns the ordinary module $Q(g)$. No rational-function data or distinguished index appears in this theorem.
-- source:
--   Guo, Wang & Zheng, Exploiting Sign Symmetries in Minimizing Sums of Rational Functions, arXiv:2405.09419v1, p. 12, Theorem 4.5 [29, Theorem 6.11]

import Mathlib
import Definitions.Def_SignSymRat_Hierarchy_SparseQM

open MvPolynomial

namespace SignSymRat.Hierarchy

/-- Theorem 4.5, p. 12: the sign-symmetric Putinar representation. -/
theorem theorem_4_5 {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
    (f : MvPolynomial (Fin n) ℝ) (hArch : IsArchimedean g)
    (hpos : ∀ x ∈ semialgK g, 0 < eval x f) :
    ∃ k : ℕ,
      f ∈ sparseQM g (f.support ∪ Finset.univ.biUnion (fun j : Fin m => (g j).support)) k := by sorry

end SignSymRat.Hierarchy
