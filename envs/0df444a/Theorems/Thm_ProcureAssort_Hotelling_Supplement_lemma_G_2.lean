-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_Supplement_lemma_G_2
-- name    : ProcureAssort.Hotelling.Supplement.lemma_G_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T12:32:15.821083+00:00
-- url     : https://prove2.me/theorems/2523620b-6658-4b7b-b23e-5d9d064a31a6
-- title:
--   Lemma G.2 — Active affine demand formula
-- statement:
--   In a nonempty affine product market, let $p$ be any price vector and let $Q=\{i:d_i(N,p)>0\}$. Write $D=\Gamma^{-1}$, $c=\Gamma^{-1}\alpha$, $F=(D_Q)^{-1}$ and let $\mathbf1$ be the all-ones vector on $Q$. Then $Q$ is nonempty, demand is consumer optimal, demand on $N$ equals demand restricted to $Q$, $\mathbf1^\top F\mathbf1>0$, and
--
--   $$d_Q(p)=F\left(c_Q-p_Q+\frac{1-\mathbf1^\top F(c_Q-p_Q)}{\mathbf1^\top F\mathbf1}\mathbf1\right).$$
--
--   The formula applies to the active subvector, including a singleton active set, and supplies the coefficients used by the affine implementation system.
--
--   Differences from the source:
--
--   - encoding: the positive demand subvector in (22) → full and restricted demand agree, with the displayed formula on the active subtype and a positive denominator; reason: zero quantities off the active set are retained; strict concavity and unit total consumption exclude empty active sets and division by zero
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Lemma G.2, p. 48

import Definitions.Def_ProcureAssort_Hotelling_Supplement_Affine

namespace ProcureAssort.Hotelling.Supplement

theorem lemma_G_2 (n : ℕ) (hn : 0 < n) (M : QuadraticMarket (Fin n))
    (hM : M.Valid) (p : Fin n → ℝ) :
    let Q := M.active p
    Q.Nonempty ∧
    M.IsDemand Finset.univ p (M.demand Finset.univ p) ∧
    M.demand Finset.univ p = M.demand Q p ∧
    0 < (∑ i : Q, ∑ j : Q, M.faceF Q i j) ∧
    ∀ i : Q, M.demand Finset.univ p i = M.faceDemand Q p i := by sorry

end ProcureAssort.Hotelling.Supplement
