-- Prove2me | Theorems.Thm_ProcessingNetworks_CTMCFoster_theorem_D_17
-- name    : ProcessingNetworks.CTMCFoster.theorem_D_17
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:27:40.893352+00:00
-- url     : https://prove2.me/theorems/627e8e06-f3ce-4139-ab79-dc8b52d23a41
-- title:
--   Theorem D.17 — positive recurrence and stationary distributions of an irreducible continuous-time chain
-- statement:
--   Let $\Lambda$ be a regular generator on a countable state space $\mathscr S$, with exit rates $\lambda(i)$, and suppose $\Lambda$ is irreducible. Let $X$ be the continuous-time Markov chain with generator $\Lambda$ and $T_i$ its first passage time to $i$. The following are equivalent:
--
--   1. every state is positive recurrent;
--   2. some state is positive recurrent;
--   3. there exists a stationary distribution for $X$.
--
--   When these hold, the stationary distribution $\pi$ is unique and
--
--   $$
--   \pi(i)=\frac1{\lambda(i)\,\mathbb E_i(T_i)},\qquad i\in\mathscr S.
--   $$
--
--   This is the continuous-time counterpart of Theorem C.19. It identifies the stationary distribution through mean return times, and it is where regularity matters: an explosive chain may have an invariant distribution without being positive recurrent.
--
--   Differences from the source:
--   - encoding: "All generator matrices are assumed to be regular hereafter" (Definition D.3) → the explicit hypotheses `IsGeneratorC Λ` and `NonExplosive`; reason: the standing assumption of §§D.3–D.7 is written into the binders
--   - encoding: the state space is nonempty by convention → `[Nonempty S]`; reason: on an empty type statement (i) would hold vacuously while (iii) fails
--   - encoding: state $i$ positive recurrent, $\mathbb E_i(T_i)<\infty$ with $T_i$ from (D.15) → `Recurrent` of the jump chain together with `meanReturnTime < ⊤`; reason: the published definition computes $\mathbb E_i(T_i)$ from the construction (D.5)–(D.6), and non-return is the separate clause
--   - encoding: $\pi$ invariant for $\Lambda$ → `Stability.IsStationaryDistribution` of $G$ and $\lambda$; reason: the published predicate is $\pi\Lambda=0$ written out through $\Lambda_{xy}=\lambda(x)G_{xy}$
--   - encoding: "when these equivalent conditions are satisfied" → a universal statement over stationary distributions $\pi$; reason: the three conditions are equivalent, and (iii) provides the $\pi$
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Theorem D.17, eq. (D.20), p.293 (PDF 309); Definitions D.15, D.16, p.293; Definition D.3, p.289 (PDF 305)

import Mathlib
import Definitions.Def_MatrixAnalytic_ProductForm_Chain
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions
import Definitions.Def_ProcessingNetworks_CTMCFoster_jumpPMF
import Definitions.Def_ProcessingNetworks_CTMCFoster_NonExplosive

namespace ProcessingNetworks.CTMCFoster

open MatrixAnalytic.ProductForm
open scoped ENNReal

/-- Theorem D.17. If the regular generator `Λ` is irreducible, the following are equivalent:
(i) every state is positive recurrent; (ii) some state is positive recurrent; (iii) there exists a
stationary distribution for `X`. When they hold, the stationary distribution is unique and
`π(i) = 1 / (λ(i) E_i(T_i))` (D.20).

Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Theorem D.17,
eq. (D.20), p.293 (PDF 309).

**Formalization Note** Regularity (Definition D.3, the standing assumption of §§D.3–D.7) is
`IsGeneratorC Λ` (Definition D.1 and (D.2)) together with `NonExplosive`. A state `i` is positive
recurrent when `Recurrent (jumpPMF hΛ) i ∧ meanReturnTime (jumpPMF hΛ) (holdRate Λ) i < ⊤`, the
per-state clause of `Stability.PositiveRecurrent`. Since (i), (ii), (iii) are equivalent, "when
these conditions are satisfied" is expressed by quantifying over a stationary distribution `π`.
`Nonempty S` is needed: on an empty type (i) holds vacuously and (iii) fails. -/
theorem theorem_D_17 {S : Type*} [Countable S] [Nonempty S] [DecidableEq S] {Λ : S → S → ℝ}
    (hΛ : IsGeneratorC Λ) (hreg : NonExplosive (jumpPMF hΛ) (holdRate Λ))
    (hirr : Stability.Irreducible (jumpPMF hΛ)) :
    List.TFAE
        [Stability.PositiveRecurrent (jumpPMF hΛ) (holdRate Λ),
          ∃ i : S, Stability.Recurrent (jumpPMF hΛ) i ∧
            Stability.meanReturnTime (jumpPMF hΛ) (holdRate Λ) i < ⊤,
          ∃ π : PMF S, Stability.IsStationaryDistribution (jumpPMF hΛ) (holdRate Λ) π] ∧
      ∀ π : PMF S, Stability.IsStationaryDistribution (jumpPMF hΛ) (holdRate Λ) π →
        (∀ π' : PMF S, Stability.IsStationaryDistribution (jumpPMF hΛ) (holdRate Λ) π' → π' = π) ∧
          ∀ i : S, π i = (ENNReal.ofReal (holdRate Λ i) *
            Stability.meanReturnTime (jumpPMF hΛ) (holdRate Λ) i)⁻¹ := by sorry

end ProcessingNetworks.CTMCFoster
