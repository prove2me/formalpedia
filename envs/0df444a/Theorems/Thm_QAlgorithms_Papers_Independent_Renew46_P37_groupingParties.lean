-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_groupingParties
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.groupingParties
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T22:13:42.639631+00:00
-- url     : https://prove2.me/theorems/5e3302cd-6ff0-4803-925d-fa5cd88cbe68
-- title:
--   Grouping disjoint parties preserves a secrecy monotone
-- statement:
--   Let $m>n\ge2$, and let $g:\{1,\ldots,m\}\to\{1,\ldots,n\}$ be surjective. If $M$ is an $n$-party secrecy monotone on arbitrary finite alphabets, define $M_g(P)$ by grouping all fine-party variables in the same fiber of $g$ and evaluating $M$. Then
--   $$M_g\text{ is an }m\text{-party secrecy monotone}.$$
--   All laws are normalized; local alphabets are nonempty. Local fine-party operations stay inside one coarse block, and public messages are known to Eve and conditioned upon.
--
--   The fibers give disjoint, nonempty groups; overlapping groups are not included.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, PDF p. 4, §II.B.3

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P37

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Claimed50.P33
  (InformationKind RegisterBasis FiniteState singleParties allParties
   info entropyAt trivialExtension informationFunctional LocalInstrument
   IsContinuousFunctional partyProduct registerMarginal)

/-- §II.B.3, PDF p.4: a surjective grouping of disjoint fine parties extends
a coarse monotone. Fine parties never act across different coarse blocks. -/
theorem groupingParties {m n : ℕ} (hn : 2 ≤ n) (hm : n < m)
    (g : Fin m → Fin n) (hg : Function.Surjective g) (M : CData n → ℝ)
    (hM : IsCMonotone M) : IsCMonotone (fun p => M (groupData g p)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
