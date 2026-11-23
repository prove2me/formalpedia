-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_Supplement_theorem_4_2
-- name    : ProcureAssort.Hotelling.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:30:03.836001+00:00
-- url     : https://prove2.me/theorems/825fb4b3-0868-42d0-8ac5-d4f71c66a1dc
-- title:
--   Theorem 4.2 — Affine linear-pricing implementation
-- statement:
--   Let $n\ge2$ suppliers have independent regular finite cost distributions. In the affine model let $\alpha\ge0$ and let $\Gamma$ be symmetric positive definite, have nonpositive off-diagonal entries, and be strictly diagonally dominant. Consumption is the unit simplex. Write $x^*(\theta)=d(N,v(\theta))$ and $Q(\theta)=\{i:x_i^*(\theta)>0\}$.
--
--   Suppose a profile $\theta$ and a real $d^*$ satisfy $Q(\theta)=N$ and $Q(\theta')=N$ whenever $|v_i(\theta_i')-v_i(\theta_i)|\le d^*$ for every supplier. Suppose also that every supplier has at least three supported costs and every adjacent virtual-cost increment is at most $d^*/2$. Then
--
--   $$OPT(DecLin)=OPT(Cent).$$
--
--   This is the affine companion to the mission's published Hotelling goal. The same witness $d^*$ occurs in both conditions; no all-active maximal profile is assumed.
--
--   Differences from the source:
--
--   - encoding: finite suppliers and supported independent costs → Fin n, nonempty finite positive supports and positive normalized probabilities; regularity on supported types; reason: zero-based indexing and explicit standing assumptions of §2 and Assumption 3.1, with no change to admissible distributions
--   - encoding: OPT denotes an actual optimal value → equality of the published real suprema together with nonempty bounded-above feasible objective sets; reason: compact finite-dimensional consumption and interim IR bound the objectives; the extra clauses rule out junk real suprema without assuming boundedness
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Theorem 4.2, p. 25

import Definitions.Def_ProcureAssort_Hotelling_Supplement_Affine

namespace ProcureAssort.Hotelling.Supplement

theorem theorem_4_2 (n : ℕ) (hn : 2 ≤ n) (M : QuadraticMarket (Fin n))
    (hM : M.Valid) (hDD : M.StrictDD) (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ)
    (hTypes : ValidTypes Θ f) (hReg : Regular Θ f)
    (hConditions : ∃ (θ : Profile Θ) (d : ℝ),
      affQ M Θ f θ = Finset.univ ∧
      (∀ θ' : Profile Θ, (∀ i, |virtualCost Θ f i (θ' i) - virtualCost Θ f i (θ i)| ≤ d) →
        affQ M Θ f θ' = Finset.univ) ∧
      (∀ i, 3 ≤ (Θ i).card) ∧
      (∀ i, ∀ a b : ℝ, Consecutive (Θ i) a b →
        virtualCost Θ f i b - virtualCost Θ f i a ≤ d / 2)) :
    optDecLin Θ f M.gcs (simplex n) = optCent Θ f M.gcs (simplex n) ∧
      ValuesWellDefined Θ f M.gcs := by sorry

end ProcureAssort.Hotelling.Supplement
