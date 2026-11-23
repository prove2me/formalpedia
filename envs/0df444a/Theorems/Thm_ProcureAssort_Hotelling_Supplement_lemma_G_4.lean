-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_Supplement_lemma_G_4
-- name    : ProcureAssort.Hotelling.Supplement.lemma_G_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:35:18.228774+00:00
-- url     : https://prove2.me/theorems/42a815c8-429e-442b-a5cd-c3924c6d168d
-- title:
--   Lemma G.4 — Symmetry and exact affine rank
-- statement:
--   In the affine model, fix a profile $\theta$ with every supplier active, and let $A$ be the active demand coefficient matrix of Corollary G.1. Then
--
--   $$A^\top=A,\qquad \operatorname{rank}(A)=n-1.$$
--
--   The exact rank records the single redundant demand equation and the remaining common-price freedom. Strict diagonal dominance is not added to the affine standing assumptions.
--
--   Differences from the source:
--
--   - encoding: finite suppliers and supported independent costs → Fin n, nonempty finite positive supports and positive normalized probabilities; regularity on supported types; reason: zero-based indexing and explicit standing assumptions of §2 and Assumption 3.1, with no change to admissible distributions
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Lemma G.4, p. 51

import Definitions.Def_ProcureAssort_Hotelling_Supplement_Affine

namespace ProcureAssort.Hotelling.Supplement

theorem lemma_G_4 (n : ℕ) (hn : 0 < n) (M : QuadraticMarket (Fin n))
    (hM : M.Valid) (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ)
    (hTypes : ValidTypes Θ f) (hReg : Regular Θ f) (θ : Profile Θ)
    (hActive : affQ M Θ f θ = Finset.univ) :
    let A := M.faceA (affQ M Θ f θ)
    A.IsSymm ∧ A.rank = n - 1 := by sorry

end ProcureAssort.Hotelling.Supplement
