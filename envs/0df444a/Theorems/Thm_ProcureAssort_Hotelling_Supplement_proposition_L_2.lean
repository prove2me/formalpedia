-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_Supplement_proposition_L_2
-- name    : ProcureAssort.Hotelling.Supplement.proposition_L_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:38:22.187462+00:00
-- url     : https://prove2.me/theorems/a52172a5-12b4-46c5-af13-7aeb7ab8963d
-- title:
--   Proposition L.2 — Hotelling row-dependence prefix identities
-- statement:
--   Let a Hotelling market have ordered locations in $[0,1]$, positive transportation cost $\delta$, and independent regular finite costs. Let $(a,b)$ satisfy (20), with $a$ expressed in the consecutive-active price-difference row coordinates. At every profile,
--
--   $$\sum_{j\in Q(\theta)}b_j(\theta_j)f_{-j}(\theta_{-j})x_j^*(\theta)=0,$$
--
--   and, for each nonlast active supplier $i$,
--
--   $$a_i(\theta)=\sum_{j\in Q(\theta):j\le i}b_j(\theta_j)f_{-j}(\theta_{-j})x_j^*(\theta).$$
--
--   These identities supply the transfer and demand-row cancellations used by the common-distribution Hotelling result.
--
--   Differences from the source:
--
--   - encoding: finite suppliers and supported independent costs → Fin n, nonempty finite positive supports and positive normalized probabilities; regularity on supported types; reason: zero-based indexing and explicit standing assumptions of §2 and Assumption 3.1, with no change to admissible distributions
--   - reading: the coefficients a in (20), (40) → a multiplies the consecutive-active price-difference rows p_next minus p_i; reason: Appendix L.3 p. 78 telescopes precisely these rows; using the base path-matrix rows would make the prefix formula a different claim
--   - generalization: the setting of Theorem H.1 (equidistant locations, identical cost distributions), in which Proposition L.2 is stated (Appendix L.3, p. 75) → any strictly increasing locations in [0,1] and independent, possibly non-identical, regular finite cost distributions; reason: the identities follow from (20) column by column for any active set and allocation; with equiLoc n and one shared support and pmf the statement is exactly the source's
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Proposition L.2, p. 75

import Definitions.Def_ProcureAssort_Hotelling_Supplement_CommonHotelling

namespace ProcureAssort.Hotelling.Supplement

theorem proposition_L_2 (n : ℕ) (hn : 2 ≤ n) (Θ : Fin n → Finset ℝ)
    (f : Fin n → ℝ → ℝ) (hTypes : ValidTypes Θ f) (hReg : Regular Θ f)
    (loc : Fin n → ℝ) (hloc : StrictMono loc) (hunit : ∀ i, loc i ∈ Set.Icc (0 : ℝ) 1)
    (delta : ℝ) (hdelta : 0 < delta)
    (a : Profile Θ → Fin n → ℝ) (b : Fin n → ℝ → ℝ)
    (hDep : RowDependence f (activeSet Θ f loc delta) (xstar Θ f loc delta)
      (fun θ => differenceA (activeSet Θ f loc delta θ)) a b) :
    ∀ θ : Profile Θ,
      (∑ j ∈ activeSet Θ f loc delta θ,
        b j (θ j) * probOthers f j θ * xstar Θ f loc delta θ j) = 0 ∧
      ∀ i, ReducedRow (activeSet Θ f loc delta θ) i →
        a θ i = ∑ j ∈ (activeSet Θ f loc delta θ).filter (· ≤ i),
          b j (θ j) * probOthers f j θ * xstar Θ f loc delta θ j := by sorry

end ProcureAssort.Hotelling.Supplement
