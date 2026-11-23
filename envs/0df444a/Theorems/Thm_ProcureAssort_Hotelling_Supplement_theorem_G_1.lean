-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_Supplement_theorem_G_1
-- name    : ProcureAssort.Hotelling.Supplement.theorem_G_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:36:44.927807+00:00
-- url     : https://prove2.me/theorems/f4d228c2-2e39-42ca-972e-7125d73cd313
-- title:
--   Theorem G.1 — RIOM affine implementation
-- statement:
--   Consider the general affine market with independent regular finite cost distributions. Assume $\alpha\ge0$, symmetric positive definite $\Gamma$ with nonpositive off-diagonal entries, and unit simplex consumption. If the market is RIOM in the exact sense of Definitions G.3–G.4, then
--
--   $$OPT(DecLin)=OPT(Cent).$$
--
--   RIOM includes an all-active product box of discrete intervals with at least three types per coordinate and the source's existential reachability condition. The theorem allows arbitrary supplier distributions and does not require strict diagonal dominance.
--
--   Differences from the source:
--
--   - encoding: finite suppliers and supported independent costs → Fin n, nonempty finite positive supports and positive normalized probabilities; regularity on supported types; reason: zero-based indexing and explicit standing assumptions of §2 and Assumption 3.1, with no change to admissible distributions
--   - encoding: OPT denotes an actual optimal value → equality of the published real suprema together with nonempty bounded-above feasible objective sets; reason: compact finite-dimensional consumption and interim IR bound the objectives; the extra clauses rule out junk real suprema without assuming boundedness
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Theorem G.1, p. 56

import Definitions.Def_ProcureAssort_Hotelling_Supplement_Affine

namespace ProcureAssort.Hotelling.Supplement

theorem theorem_G_1 (n : ℕ) (hn : 0 < n) (M : QuadraticMarket (Fin n))
    (hM : M.Valid) (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ)
    (hTypes : ValidTypes Θ f) (hReg : Regular Θ f) (hRIOM : RIOM Θ (affQ M Θ f)) :
    optDecLin Θ f M.gcs (simplex n) = optCent Θ f M.gcs (simplex n) ∧
      ValuesWellDefined Θ f M.gcs := by sorry

end ProcureAssort.Hotelling.Supplement
