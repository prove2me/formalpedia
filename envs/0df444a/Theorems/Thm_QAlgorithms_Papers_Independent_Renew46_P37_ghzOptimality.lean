-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_ghzOptimality
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.ghzOptimality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:31:31.320425+00:00
-- url     : https://prove2.me/theorems/d8b69f2f-978c-4b25-ae94-afcce6bdba74
-- title:
--   Optimal exact one-output-per-GHZ yield
-- statement:
--   Let $k,l$ be positive integers. From $k$ independent normalized plus GHZ states, any finite local-instrument/public-communication protocol producing $l$ exact independent copies of either $P^3$ or $P^x$, secret from Eve's complete public transcript, satisfies
--   $$l\le k.$$
--   For every positive $k$, equality is attainable for either target by the corresponding independent local basis measurements. Inputs and outputs are regrouped by labelled party, using fixed finite word codings.
--
--   This is the finite exact block theorem. No approximate asymptotic rate is inferred without an error metric and continuity modulus.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, PDF p. 11, §V.D–E, (66)–(73)

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

/-- §V.D--E, PDF pp.11--12: k GHZ copies produce at most k exact secret
copies of either target. For every positive k equality is attained by local
basis measurements. This is a finite exact theorem, not an unspecified
approximate-rate limit. -/
theorem ghzOptimality :
    (∀ (k l : ℕ), 0 < k → 0 < l →
      ∀ s : FiniteState 3,
      s.dims = (fun _ => Fintype.card (Fin k → Fin 2)) →
      (∃ e : (i : Fin 3) → Fin (s.dims i) ≃ Fin (Fintype.card (Fin k → Fin 2)),
        ∀ x y, s.rho x y =
          pureDensity (ghzCopiesVector k) (fun i => e i (x i)) (fun i => e i (y i))) →
      ∀ target : Fin 2,
        QExtracts s (cCopies (exampleLaw (if target = 0 then 3 else 4)) l) → l ≤ k) ∧
    (∀ k : ℕ, 0 < k → ∃ s : FiniteState 3,
      s.dims = (fun _ => Fintype.card (Fin k → Fin 2)) ∧
      (∃ e : (i : Fin 3) → Fin (s.dims i) ≃ Fin (Fintype.card (Fin k → Fin 2)),
        ∀ x y, s.rho x y =
          pureDensity (ghzCopiesVector k) (fun i => e i (x i)) (fun i => e i (y i))) ∧
      ∀ target : Fin 2,
        QExtracts s (cCopies (exampleLaw (if target = 0 then 3 else 4)) k)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
