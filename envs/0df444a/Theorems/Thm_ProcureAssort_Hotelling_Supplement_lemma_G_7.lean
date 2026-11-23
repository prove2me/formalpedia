-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_Supplement_lemma_G_7
-- name    : ProcureAssort.Hotelling.Supplement.lemma_G_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:36:09.950985+00:00
-- url     : https://prove2.me/theorems/4924cb5f-8365-4a12-8e84-66c9ddd2b3f3
-- title:
--   Lemma G.7 — Weighted affine allocation identity
-- statement:
--   In the affine model let $(a,b)$ be any coefficient vector satisfying row dependence (20) in the reduced demand-and-interim-transfer pricing system. For each supported cost define $g_i(c)=b_i(c)/f_i(c)$. Then every profile satisfies
--
--   $$\sum_{i\in Q(\theta)}g_i(\theta_i)x_i^*(\theta)=0.$$
--
--   This identity links pricing row dependencies to centralized quantities. It imposes no vanishing condition on coefficients attached to identically zero transfer rows.
--
--   Differences from the source:
--
--   - encoding: finite suppliers and supported independent costs → Fin n, nonempty finite positive supports and positive normalized probabilities; regularity on supported types; reason: zero-based indexing and explicit standing assumptions of §2 and Assumption 3.1, with no change to admissible distributions
--   - encoding: row dependence (20) → one equality per active price column, with the last active demand row omitted; reason: the full coefficient sum is zero exactly when each column coefficient is zero; inactive price columns are discarded on p. 47
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Lemma G.7, p. 55

import Definitions.Def_ProcureAssort_Hotelling_Supplement_Affine

namespace ProcureAssort.Hotelling.Supplement

theorem lemma_G_7 (n : ℕ) (hn : 0 < n) (M : QuadraticMarket (Fin n))
    (hM : M.Valid) (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ)
    (hTypes : ValidTypes Θ f) (hReg : Regular Θ f)
    (a : Profile Θ → Fin n → ℝ) (b : Fin n → ℝ → ℝ)
    (hDep : RowDependence f (affQ M Θ f) (affX M Θ f) (affA M Θ f) a b) :
    ∀ θ : Profile Θ, ∑ i ∈ affQ M Θ f θ, (b i (θ i) / f i (θ i)) * affX M Θ f θ i = 0 := by sorry

end ProcureAssort.Hotelling.Supplement
