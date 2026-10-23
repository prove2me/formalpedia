-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_classicalRelativeEntropy
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.classicalRelativeEntropy
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T22:16:09.915727+00:00
-- url     : https://prove2.me/theorems/02ccf8f0-d769-40fc-b7ec-646368d04af4
-- title:
--   The closest product law
-- statement:
--   Let $P$ be a normalized joint law on arbitrary nonempty finite alphabets for $n\ge2$ parties, and let $P_i$ denote its local marginals. With $D_2$ the relative entropy in bits, infinite when the second law vanishes on positive mass of the first,
--   $$T_n(P)=D_2(P\Vert\prod_iP_i)=\min_{Q_1,\ldots,Q_n}D_2(P\Vert\prod_iQ_i).$$
--   Every $Q_i$ is a normalized local law. The displayed product of actual marginals attains the minimum.
--
--   This is the exact closest-product characterization, with support failures retained as infinity.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, PDF p. 5, §III.B, (18)

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

/-- §III.B, PDF p.5, (18): minimum over all product laws, attained at the
product of local marginals. Source correction: D_nats/ln(2) is used, because
the printed ln conflicts with the entropy-in-bits examples. The prose's
second Q_Ai is read as P_Ai, the actual lawMarginal. -/
theorem classicalRelativeEntropy {n : ℕ} (hn : 2 ≤ n) (p : CData n) (hp : IsValidClassicalData p) :
    classicalKL p.prob (productLaw (localLaw p)) = ENNReal.ofReal (cValue .total p) ∧
    ∀ q : (i : Fin n) → Fin (p.dims i) → ℝ,
      (∀ i, IsLaw (q i)) →
      ENNReal.ofReal (cValue .total p) ≤ classicalKL p.prob (productLaw q) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
