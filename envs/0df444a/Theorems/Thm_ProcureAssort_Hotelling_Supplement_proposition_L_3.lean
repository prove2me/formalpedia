-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_Supplement_proposition_L_3
-- name    : ProcureAssort.Hotelling.Supplement.proposition_L_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T12:40:57.648811+00:00
-- url     : https://prove2.me/theorems/0960fa96-abd6-4cde-9cfa-f06d097f9964
-- title:
--   Proposition L.3 — Common-type coefficient identity
-- statement:
--   Consider $n\ge2$ equidistant Hotelling suppliers with positive transportation cost and a shared arbitrary finite regular cost distribution on $S$. Let $(a,b)$ satisfy row dependence (20) in the independent price-difference system. For every $c\in S$,
--
--   $$b_1(c)+b_n(c)+2\sum_{i=2}^{n-1}b_i(c)=0.$$
--
--   The interior sum is empty when $n=2$. This weighted identity reflects the endpoint and interior supplier locations and is used to cancel interim transfers.
--
--   Differences from the source:
--
--   - encoding: finite suppliers and supported independent costs → Fin n, nonempty finite positive supports and positive normalized probabilities; regularity on supported types; reason: zero-based indexing and explicit standing assumptions of §2 and Assumption 3.1, with no change to admissible distributions
--   - encoding: equidistant locations and identical arbitrary distributions → equiLoc n, one shared finite support and pmf, with n at least two; reason: the denominator n minus one requires two suppliers; singleton and two-point supports remain included
--   - reading: the coefficients a in (20), (40) → a multiplies the consecutive-active price-difference rows p_next minus p_i; reason: Appendix L.3 p. 78 telescopes precisely these rows; using the base path-matrix rows would make the prefix formula a different claim
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Proposition L.3, p. 76

import Definitions.Def_ProcureAssort_Hotelling_Supplement_CommonHotelling

namespace ProcureAssort.Hotelling.Supplement

theorem proposition_L_3 (n : ℕ) (hn : 2 ≤ n) (S : Finset ℝ) (f : ℝ → ℝ)
    (hTypes : ValidTypes (fun _ : Fin n => S) (fun _ => f))
    (hReg : Regular (fun _ : Fin n => S) (fun _ => f)) (delta : ℝ) (hdelta : 0 < delta)
    (a : Profile (fun _ : Fin n => S) → Fin n → ℝ) (b : Fin n → ℝ → ℝ)
    (hDep : RowDependence (fun _ : Fin n => f)
      (activeSet (fun _ => S) (fun _ => f) (equiLoc n) delta)
      (xstar (fun _ => S) (fun _ => f) (equiLoc n) delta)
      (fun θ => differenceA (activeSet (fun _ => S) (fun _ => f) (equiLoc n) delta θ)) a b) :
    ∀ c ∈ S, b ⟨0,by omega⟩ c + b ⟨n-1,by omega⟩ c +
      2 * (∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => 0 < i.val ∧ i.val < n-1), b i c) = 0 := by sorry

end ProcureAssort.Hotelling.Supplement
