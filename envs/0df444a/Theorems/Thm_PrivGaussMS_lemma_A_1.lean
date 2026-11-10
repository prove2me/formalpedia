-- Prove2me | Theorems.Thm_PrivGaussMS_lemma_A_1
-- name    : PrivGaussMS.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:07:58.860354+00:00
-- url     : https://prove2.me/theorems/7a65b6e6-ab33-4d9f-8c18-e57903460f79
-- title:
--   Lemma A.1 — coupling inequality, maximal coupling, and data processing for total variation
-- statement:
--   Let $P,Q$ be probability laws. A coupling of $P,Q$ is a jointly defined pair $(U,V)$ with respective distributions $P,Q$. Every coupling satisfies
--   $$\mathrm{TV}(P,Q)\le\mathbb P\{U\ne V\},$$
--   and there exists a coupling attaining equality. Moreover, applying the same fixed randomized rule $K$ to either distribution cannot increase total variation distance:
--   $$\mathrm{TV}(\mathcal L(K(U)),\mathcal L(K(V)))\le\mathrm{TV}(P,Q).$$
--
--   Differences from the source:
--   - reading: 'P{U ≠ V}' for laws on an unspecified space → the diagonal of the space is assumed measurable (true on ℝ^k and every standard Borel space); reason: the event {U ≠ V} must be measurable for the statement to make sense
--   - encoding: a coupling; a fixed randomized rule K → a measure on pairs with the two marginals; a Markov kernel; reason: standard definitions
-- source:
--   Moayedi, Yassaee, Ebrahimi, Optimal Private Gaussian Multi-sampling, STOC 2027 submission (manuscript sha256 1838c582…), Lemma A.1, p.23

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_tvDist

open MeasureTheory ProbabilityTheory

namespace PrivGaussMS

/-- **Lemma A.1** (Coupling and postprocessing for total variation), Moayedi, Yassaee, Ebrahimi,
*Optimal Private Gaussian Multi-sampling*, STOC 2027 submission (manuscript sha256 1838c582…),
p.23.

For probability measures `P, Q`: every coupling `(U, V)` (a law on pairs with marginals `P, Q`)
satisfies `TV(P, Q) ≤ P{U ≠ V}`; some coupling attains equality; and a fixed randomized rule `K`
(a Markov kernel) applied to either law does not increase total variation distance.

**Formalization Note.** `TV(P, Q) = sup_E |P(E) − Q(E)|` is the published `tvDist`. The event
`{U ≠ V}` must be measurable, so the diagonal of `α × α` is assumed measurable (true on `ℝ^k` and
every standard Borel space). -/
theorem lemma_A_1 {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (hdiag : MeasurableSet (Set.diagonal α))
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    (∀ γ : Measure (α × α), γ.map Prod.fst = P → γ.map Prod.snd = Q →
        FoundationsRL.DECLower.tvDist P Q ≤ γ.real {p | p.1 ≠ p.2}) ∧
    (∃ γ : Measure (α × α), γ.map Prod.fst = P ∧ γ.map Prod.snd = Q ∧
        FoundationsRL.DECLower.tvDist P Q = γ.real {p | p.1 ≠ p.2}) ∧
    (∀ K : Kernel α β, IsMarkovKernel K →
        FoundationsRL.DECLower.tvDist (P.bind K) (Q.bind K) ≤
          FoundationsRL.DECLower.tvDist P Q) := by sorry

end PrivGaussMS
