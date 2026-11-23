-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_Supplement_lemma_L_2
-- name    : ProcureAssort.Hotelling.Supplement.lemma_L_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:42:39.491326+00:00
-- url     : https://prove2.me/theorems/f269be3a-6773-4a79-9b94-aca9c37a8b98
-- title:
--   Lemma L.2 — Narrow common virtual-cost range
-- statement:
--   In the setting of Theorem H.1, let $\underline\theta$ and $\bar\theta$ be the minimum and maximum of the shared nonempty support. If
--
--   $$v(\bar\theta)-v(\underline\theta)\le\frac{\delta}{n-1},$$
--
--   then $OPT(DecLin)=OPT(Cent)$. This is the narrow-range case, including a singleton support and the equality boundary.
--
--   Differences from the source:
--
--   - encoding: finite suppliers and supported independent costs → Fin n, nonempty finite positive supports and positive normalized probabilities; regularity on supported types; reason: zero-based indexing and explicit standing assumptions of §2 and Assumption 3.1, with no change to admissible distributions
--   - encoding: equidistant locations and identical arbitrary distributions → equiLoc n, one shared finite support and pmf, with n at least two; reason: the denominator n minus one requires two suppliers; singleton and two-point supports remain included
--   - encoding: OPT denotes an actual optimal value → equality of the published real suprema together with nonempty bounded-above feasible objective sets; reason: compact finite-dimensional consumption and interim IR bound the objectives; the extra clauses rule out junk real suprema without assuming boundedness
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Lemma L.2, p. 76

import Definitions.Def_ProcureAssort_Hotelling_Supplement_CommonHotelling

namespace ProcureAssort.Hotelling.Supplement

theorem lemma_L_2 (n : ℕ) (hn : 2 ≤ n) (S : Finset ℝ) (f : ℝ → ℝ)
    (hTypes : ValidTypes (fun _ : Fin n => S) (fun _ => f))
    (hReg : Regular (fun _ : Fin n => S) (fun _ => f)) (delta : ℝ) (hdelta : 0 < delta)
    (hRange : commonRange (n := n) S f ⟨0,by omega⟩ ≤ delta / (n-1 : ℕ)) :
    optDecLin (fun _ : Fin n => S) (fun _ => f) (hotGCS (equiLoc n) delta) (simplex n) =
      optCent (fun _ : Fin n => S) (fun _ => f) (hotGCS (equiLoc n) delta) (simplex n) ∧
    ValuesWellDefined (fun _ : Fin n => S) (fun _ => f) (hotGCS (equiLoc n) delta) := by sorry

end ProcureAssort.Hotelling.Supplement
