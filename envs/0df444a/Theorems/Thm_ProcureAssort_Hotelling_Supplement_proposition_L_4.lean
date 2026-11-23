-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_Supplement_proposition_L_4
-- name    : ProcureAssort.Hotelling.Supplement.proposition_L_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:42:09.968661+00:00
-- url     : https://prove2.me/theorems/1624b47c-3bde-4194-ac36-848e8754fc13
-- title:
--   Proposition L.4 — Vanishing coefficients below the top virtual cost
-- statement:
--   In the equidistant, identical-distribution setting of Theorem H.1, suppose $(a,b)$ satisfies row dependence (20). Let $\bar\theta=\max S$ and let $v$ be the common virtual-cost function. For every supported cost $c$,
--
--   $$v(\bar\theta)-v(c)\ge\frac{\delta}{n-1}\quad\Longrightarrow\quad b_i(c)=0\quad\text{for all }i.$$
--
--   The bound includes equality. It identifies coefficients below the top virtual-cost band without imposing any restriction on support cardinality.
--
--   Differences from the source:
--
--   - encoding: finite suppliers and supported independent costs → Fin n, nonempty finite positive supports and positive normalized probabilities; regularity on supported types; reason: zero-based indexing and explicit standing assumptions of §2 and Assumption 3.1, with no change to admissible distributions
--   - encoding: equidistant locations and identical arbitrary distributions → equiLoc n, one shared finite support and pmf, with n at least two; reason: the denominator n minus one requires two suppliers; singleton and two-point supports remain included
--   - reading: the coefficients a in (20), (40) → a multiplies the consecutive-active price-difference rows p_next minus p_i; reason: Appendix L.3 p. 78 telescopes precisely these rows; using the base path-matrix rows would make the prefix formula a different claim
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Proposition L.4, p. 76

import Definitions.Def_ProcureAssort_Hotelling_Supplement_CommonHotelling

namespace ProcureAssort.Hotelling.Supplement

theorem proposition_L_4 (n : ℕ) (hn : 2 ≤ n) (S : Finset ℝ) (f : ℝ → ℝ)
    (hTypes : ValidTypes (fun _ : Fin n => S) (fun _ => f))
    (hReg : Regular (fun _ : Fin n => S) (fun _ => f)) (delta : ℝ) (hdelta : 0 < delta)
    (a : Profile (fun _ : Fin n => S) → Fin n → ℝ) (b : Fin n → ℝ → ℝ)
    (hDep : RowDependence (fun _ : Fin n => f)
      (activeSet (fun _ => S) (fun _ => f) (equiLoc n) delta)
      (xstar (fun _ => S) (fun _ => f) (equiLoc n) delta)
      (fun θ => differenceA (activeSet (fun _ => S) (fun _ => f) (equiLoc n) delta θ)) a b) :
    ∀ c ∈ S,
      virtualCost (fun _ : Fin n => S) (fun _ => f) ⟨0,by omega⟩ (S.max' (hTypes.1 ⟨0,by omega⟩)) -
        virtualCost (fun _ : Fin n => S) (fun _ => f) ⟨0,by omega⟩ c ≥ delta / (n-1 : ℕ) →
      ∀ i, b i c = 0 := by sorry

end ProcureAssort.Hotelling.Supplement
