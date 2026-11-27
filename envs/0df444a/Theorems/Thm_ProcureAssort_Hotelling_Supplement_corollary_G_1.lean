-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_Supplement_corollary_G_1
-- name    : ProcureAssort.Hotelling.Supplement.corollary_G_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T12:34:33.57171+00:00
-- url     : https://prove2.me/theorems/202b591a-0ddb-4dad-8c0f-3b1b61b412be
-- title:
--   Corollary G.1 — Affine price coefficients
-- statement:
--   At any type profile $\theta$, let $Q=Q(\theta)$ and $F=(D_Q)^{-1}$ in the affine market. For every active row $i$ and active column $j$, the coefficient of $p_j$ in row $i$ is
--
--   $$A_{ij}=-F_{ij}+\frac{(\sum_{k\in Q}F_{kj})(\sum_{k\in Q}F_{ik})}{\sum_{k,l\in Q}F_{kl}}.$$
--
--   The coefficient is extracted from the fixed-face affine demand expression, rather than defined to equal the displayed right-hand side. This identifies the actual demand coefficients needed by the pricing system.
--
--   Differences from the source:
--
--   - encoding: finite suppliers and supported independent costs → Fin n, nonempty finite positive supports and positive normalized probabilities; regularity on supported types; reason: zero-based indexing and explicit standing assumptions of §2 and Assumption 3.1, with no change to admissible distributions
--   - reading: 1 ≤ i ≤ Q(θ) → i belongs to the active subtype Q(θ); reason: the rows of F and A are indexed by the active suppliers, as specified in Definition G.2 on p. 49
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Corollary G.1, p. 49

import Definitions.Def_ProcureAssort_Hotelling_Supplement_Affine

namespace ProcureAssort.Hotelling.Supplement

theorem corollary_G_1 (n : ℕ) (hn : 0 < n) (M : QuadraticMarket (Fin n))
    (hM : M.Valid) (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ)
    (hTypes : ValidTypes Θ f) (hReg : Regular Θ f) (θ : Profile Θ) :
    let Q := affQ M Θ f θ
    let F := M.faceF Q
    ∀ i j : Q, M.faceA Q i j = -F i j +
      ((∑ k : Q, F k j) * (∑ k : Q, F i k)) / (∑ k : Q, ∑ l : Q, F k l) := by sorry

end ProcureAssort.Hotelling.Supplement
