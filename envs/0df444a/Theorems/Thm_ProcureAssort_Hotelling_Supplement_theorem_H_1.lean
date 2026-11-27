-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_Supplement_theorem_H_1
-- name    : ProcureAssort.Hotelling.Supplement.theorem_H_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T12:44:06.206493+00:00
-- url     : https://prove2.me/theorems/3bbcf393-6ff4-45dd-8f6c-bc3d07aad858
-- title:
--   Theorem H.1 — Equidistant suppliers with identical distributions
-- statement:
--   Let $n\ge2$ Hotelling suppliers be located at $\ell_i=(i-1)/(n-1)$ and let $\delta>0$ be the transportation cost. Suppose their independent private costs have the same arbitrary finite regular distribution on a nonempty positive support. Then
--
--   $$OPT(DecLin)=OPT(Cent).$$
--
--   The result includes singleton and two-point supports. It imposes neither a thin-grid condition nor a bound on the total virtual-cost range.
--
--   Differences from the source:
--
--   - encoding: finite suppliers and supported independent costs → Fin n, nonempty finite positive supports and positive normalized probabilities; regularity on supported types; reason: zero-based indexing and explicit standing assumptions of §2 and Assumption 3.1, with no change to admissible distributions
--   - encoding: equidistant locations and identical arbitrary distributions → equiLoc n, one shared finite support and pmf, with n at least two; reason: the denominator n minus one requires two suppliers; singleton and two-point supports remain included
--   - encoding: OPT denotes an actual optimal value → equality of the published real suprema together with nonempty bounded-above feasible objective sets; reason: compact finite-dimensional consumption and interim IR bound the objectives; the extra clauses rule out junk real suprema without assuming boundedness
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Theorem H.1, p. 60

import Definitions.Def_ProcureAssort_Hotelling_Supplement_CommonHotelling

namespace ProcureAssort.Hotelling.Supplement

theorem theorem_H_1 (n : ℕ) (hn : 2 ≤ n) (S : Finset ℝ) (f : ℝ → ℝ)
    (hTypes : ValidTypes (fun _ : Fin n => S) (fun _ => f))
    (hReg : Regular (fun _ : Fin n => S) (fun _ => f)) (delta : ℝ) (hdelta : 0 < delta) :
    optDecLin (fun _ : Fin n => S) (fun _ => f) (hotGCS (equiLoc n) delta) (simplex n) =
      optCent (fun _ : Fin n => S) (fun _ => f) (hotGCS (equiLoc n) delta) (simplex n) ∧
    ValuesWellDefined (fun _ : Fin n => S) (fun _ => f) (hotGCS (equiLoc n) delta) := by sorry

end ProcureAssort.Hotelling.Supplement
