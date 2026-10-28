-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_quantumIdentities
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.quantumIdentities
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T22:24:08.746922+00:00
-- url     : https://prove2.me/theorems/0a4c3d61-94bd-4e3f-b36f-d7cceac34793
-- title:
--   Quantum entropy rewritings and basic properties
-- statement:
--   For $n\ge2$, let $\rho$ be a normalized density matrix on labelled local Hilbert spaces of arbitrary nonzero finite dimensions. Write $H(X)=S(\rho_X)$ in bits, using actual partial traces, and define $S_n=\sum_iH(A_{-i})-(n-1)H(A)$ and $T_n=\sum_iH(A_i)-H(A)$. Then
--   $$S_n=H(A)-\sum_iH(A_i\mid A_{-i})=\sum_{i=1}^{n-1}I(A_i:A_{>i}\mid A_{<i}),\qquad T_n=\sum_{i=2}^n I(A_{<i}:A_i).$$
--   The classical last-pair recurrence for $S_n$ and last-party recurrence for $T_n$ hold for $n\ge3$, and $S_n+T_n=\sum_iI(A_i:A_{-i})$. Both quantities are nonnegative, permutation invariant, zero on product density matrices, additive on independent partywise tensor products, and continuous at fixed dimensions. At $n=2$ both equal quantum mutual information.
--
--   Quantum conditional entropy is allowed to be negative; these statements impose no classical positivity on it.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, PDF p. 9, §V.B, (51),(52); cited (12),(14),(15),(19),(20),(22)

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

/-- §V.B, PDF pp.9--10, (51),(52), and the cited classical rewritings:
all entropy/chain/recurrence identities and basic properties in bits.
Quantum conditional entropy is NOT asserted nonnegative. -/
theorem quantumIdentities :
    (∀ (n : ℕ) (hn : 2 ≤ n) (s : FiniteState n),
      (∀ kind : InformationKind, 0 ≤ qValue kind s) ∧
      qValue .dual s = qH s Finset.univ -
        ∑ i, (qH s Finset.univ - qH s (Finset.univ.erase i)) ∧
      qValue .dual s = (∑ i, qH s (Finset.univ.erase i)) -
        (n-1 : ℕ) * qH s Finset.univ ∧
      qValue .total s = (∑ i, qH s {i}) - qH s Finset.univ ∧
      qValue .dual s = ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val + 1 < n),
        stateCMI s {i} (later i) (earlier i) ∧
      qValue .total s = ∑ i ∈ Finset.univ.filter (fun i : Fin n => 0 < i.val),
        stateCMI s (earlier i) {i} ∅ ∧
      (3 ≤ n → qValue .dual s = info .dual s.rho (mergeLast n) ∅ +
        stateCMI s (Finset.univ.filter fun i => i.val + 2 = n)
          (Finset.univ.filter fun i => i.val + 1 = n)
          (Finset.univ.filter fun i => i.val + 2 < n)) ∧
      (3 ≤ n → qValue .total s = info .total s.rho (firstParties n) ∅ +
        stateCMI s (Finset.univ.filter fun i => i.val + 1 = n)
          (Finset.univ.filter fun i => i.val + 1 < n) ∅) ∧
      qValue .dual s + qValue .total s = ∑ i, stateCMI s {i} (Finset.univ.erase i) ∅ ∧
      (∀ (e : Equiv.Perm (Fin n)) (kind : InformationKind),
        info kind s.rho (fun i => {e i}) ∅ = qValue kind s) ∧
      (∀ eta : (i : Fin n) → Matrix (Fin (s.dims i)) (Fin (s.dims i)) ℂ,
        (∀ i, IsDensityMatrix (eta i)) → s.rho = labelledProductDensity eta →
        ∀ kind : InformationKind, qValue kind s = 0)) ∧
    (∀ (n : ℕ), 2 ≤ n → ∀ kind : InformationKind,
      IsContinuousFunctional (qValue kind : FiniteState n → ℝ)) ∧
    (∀ (n : ℕ), 2 ≤ n → ∀ (s t : FiniteState n) (kind : InformationKind),
      info kind (partyProduct s.rho t.rho) (singleParties n) ∅ = qValue kind s + qValue kind t) ∧
    (∀ s : FiniteState 2, qValue .dual s = stateCMI s {0} {1} ∅ ∧
      qValue .total s = stateCMI s {0} {1} ∅) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
