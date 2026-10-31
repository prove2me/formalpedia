-- Prove2me | Theorems.Thm_ParriloTheta_eq_1_7
-- name    : ParriloTheta.eq_1_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:30:49.577524+00:00
-- url     : https://prove2.me/theorems/553a3f84-1092-4639-8620-e4a264317284
-- title:
--   (1.7) — $M_G\in\mathcal K^{(r)}\iff(\sum x_i^2)^rF_G\in\Sigma\iff\vartheta^{(r)}(G)=\alpha(G)\iff\vartheta\text{-rank}(G)\le r$
-- statement:
--   Let $G$ be a graph on a finite vertex set, $M_G=\alpha(G)(A_G+I)-J$ its graph matrix and $F_G(x)=(x^{\circ2})^TM_Gx^{\circ2}$ its graph polynomial. For every integer $r\ge0$,
--   $$
--   M_G\in\mathcal K^{(r)}_n\iff\Big(\sum_{i=1}^n x_i^2\Big)^{r}F_G\in\Sigma\iff\vartheta^{(r)}(G)=\alpha(G)\iff\vartheta\text{-rank}(G)\le r .
--   $$
--   These equivalences let one pass freely between the definition of the $\vartheta$-rank through the bounds $\vartheta^{(r)}$ and membership of the single matrix $M_G$ in Parrilo's cones.
--
--   Differences from the source:
--   - encoding: a graph G = (V, E) with V = [n] → G : SimpleGraph V on a finite type V; α(G) = G.indepNum; reason: Lean convention; the same graphs up to relabelling
--   - encoding: ϑ-rank(G) ∈ ℕ ∪ {∞} → thetaRank G : ℕ∞ (⊤ = ∞); reason: Lean convention; same values
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, eq. (1.7), p.2

import Mathlib
import Definitions.Def_ParriloTheta_InK
import Definitions.Def_ParriloTheta_graphMatrix
import Definitions.Def_ParriloTheta_thetaR
import Definitions.Def_ParriloTheta_thetaRank

open MvPolynomial

namespace ParriloTheta

/-- **(1.7): cone membership, sums of squares, exactness of `ϑ^(r)` and the ϑ-rank.**
Laurent & Vargas, *Exactness of Parrilo's conic approximations for copositive matrices and
associated low order bounds for the stability number of a graph*, arXiv:2109.12876v1, eq. (1.7), p.2:
"for any integer r ∈ N we have MG ∈ K(r)_n ⇐⇒ (∑_{i=1}^n x_i^2)^r FG ∈ Σ ⇐⇒ ϑ(r)(G) = α(G)
⇐⇒ ϑ-rank(G) ≤ r", where `F_G(x) = (x∘2)ᵀ M_G x∘2` (1.3).

**Formalization Note.** The three equivalences are stated as a conjunction of three iffs. The
graph lives on a finite type `V`; `α(G)` is `G.indepNum`; `Σ` is `IsSumSq`; ϑ-rank is
`ℕ∞`-valued. -/
theorem eq_1_7 {V : Type*} [Fintype V] (G : SimpleGraph V) (r : ℕ) :
    (InK r (graphMatrix G) ↔
      IsSumSq ((∑ i : V, (X i : MvPolynomial V ℝ) ^ 2) ^ r *
        ∑ i, ∑ j, C (graphMatrix G i j) * X i ^ 2 * X j ^ 2)) ∧
    (IsSumSq ((∑ i : V, (X i : MvPolynomial V ℝ) ^ 2) ^ r *
        ∑ i, ∑ j, C (graphMatrix G i j) * X i ^ 2 * X j ^ 2) ↔
      thetaR r G = (G.indepNum : ℝ)) ∧
    (thetaR r G = (G.indepNum : ℝ) ↔ thetaRank G ≤ (r : ℕ∞)) := by sorry

end ParriloTheta
