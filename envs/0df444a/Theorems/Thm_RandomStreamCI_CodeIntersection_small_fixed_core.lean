-- Prove2me | Theorems.Thm_RandomStreamCI_CodeIntersection_small_fixed_core
-- name    : RandomStreamCI.CodeIntersection.small_fixed_core
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:27:37.071377+00:00
-- url     : https://prove2.me/theorems/46d04933-8591-4b07-9473-b9be8c17e98f
-- title:
--   Corollary 12 — Small fixed core and strictly small excess mass
-- statement:
--   Let $X$ be a law on Boolean assignments to a finite $J$, with $H_\infty(X)\ge |J|-D$, $D\ge0$, and $0<\gamma,\eta<1$. For every restoring partition from Lemma 11, its parts can be divided into a core and its complementary excess group so that
--
--   $$\forall j\text{ in the core},\quad |I_j|\le\frac{D+\log_2(1/\eta)}{1-\gamma},\qquad \Pr[X\text{ lies in the excess}]<\eta.$$
--
--   Both the per-part core size bound and the strict probability bound are retained. This interface makes the support partition usable with a total list budget.
--
--   Differences from the source:
--   - encoding: coordinates and times numbered from one → Fin indices numbered from zero; reason: the order-preserving relabelling preserves every source instance
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Corollary 12, printed p. 10 / PDF p. 10

import Definitions.Def_RandomStreamCI_CodeIntersection_Probability

noncomputable section

namespace RandomStreamCI.CodeIntersection

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Corollary 12, p. 10 (20)–(21). The excess has strictly less than eta mass. -/
theorem small_fixed_core {J : Type} [Fintype J] [DecidableEq J]
    (p : PMF (J → Bool)) (γ η D : ℝ)
    (hγ : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η) (hη1 : η < 1) (hD : 0 ≤ D)
    (hentropy : (Fintype.card J : ℝ) - D ≤ minEntropy (weights p))
    (P : PartitionData J) (hP : IsRestoringPartition (weights p) γ P) :
    ∃ core : Finset (Fin P.r),
      (∀ j ∈ core, ((P.fixed j).card : ℝ) ≤ (D + log₂ (1 / η)) / (1 - γ)) ∧
      eventMass (weights p) (fun x => ∃ j : Fin P.r, j ∉ core ∧ x ∈ P.part j) < η := by sorry

end RandomStreamCI.CodeIntersection
