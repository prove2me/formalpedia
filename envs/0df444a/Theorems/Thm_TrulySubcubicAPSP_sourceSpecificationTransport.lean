-- Prove2me | Theorems.Thm_TrulySubcubicAPSP_sourceSpecificationTransport
-- name    : TrulySubcubicAPSP.sourceSpecificationTransport
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T06:13:09.197214+00:00
-- url     : https://prove2.me/theorems/9916eefb-bbe1-47ab-b577-d8730290fe16
-- title:
--   Transport of Exact Triangle, min-plus, and APSP running-time guarantees
-- statement:
--   The source and mission specifications of Exact Triangle, min-plus matrix multiplication, and all-pairs shortest paths have equivalent machine encodings. For each of these three problems $Q$ and every rational exponent $r$, the theorem transfers the source running-time claim to the mission:
--
--   $$\operatorname{SolvedInTime}_{\mathrm{source}}(Q,r)
--   \Longrightarrow \operatorname{SolvedInTime}_{\mathrm{mission}}(Q,r).$$
--
--   The transfer preserves the step bound, the word-width bound, and the quantifiers over input size and polynomial weight magnitude. For APSP it also preserves the promise that there are no negative-weight closed walks, reachability flags, and attained shortest-path distances. This connects the source formalization's algorithms to the mission's independently declared interfaces.
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/EndStatement.lean#L15-L125

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Definitions.Def_TrulySubcubicAPSP_Problems

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem TrulySubcubicAPSP.sourceSpecificationTransport :
    (∀ r : Rat, EndStatement.ExactTriangle.SolvedInTime r →
      TrulySubcubicAPSP.ExactTriangle.SolvedInTime r) ∧
    (∀ r : Rat, EndStatement.MinPlusProduct.SolvedInTime r →
      TrulySubcubicAPSP.MinPlusProduct.SolvedInTime r) ∧
    (∀ r : Rat, EndStatement.APSP.SolvedInTime r →
      TrulySubcubicAPSP.APSP.SolvedInTime r) := by sorry
