-- Prove2me | Theorems.Thm_UncertainPricing_Superrep_theorem_3_1_gamma
-- name    : UncertainPricing.Superrep.theorem_3_1_gamma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:07.596192+00:00
-- url     : https://prove2.me/theorems/ff94659f-b490-4717-9254-4c2c35876d9e
-- title:
--   Theorem 3.1 with the class Γ of p. 22 — ∃ P″ ⊂ P_m satisfying H(μ̲, μ̄) with Λ(f) = sup{E_P f : P ∈ P″} for f ∈ Γ
-- statement:
--   Assume $H(\underline\mu,\bar\mu)$ for the set $\mathbf P$ of martingale measures, with $\bar\mu$ Hölder continuous. Then there exists a subset $\mathbf P''\subset\mathbf P_m$ whose elements also satisfy $H(\underline\mu,\bar\mu)$ such that for every $f\in\Gamma$,
--   $$\Lambda(f)=\sup\{E_Pf:P\in\mathbf P''\}.$$
--
--   This is Theorem 3.1 with the class $\Gamma$ as defined in the proof ($E_Q\tilde f=E_{Q^*}f$ for every $Q\in\mathcal Q$); the mission's goal is its specialization to the explicit claim families of Lemmas 5.4–5.6.
--
--   **Formalization Note.** $\Gamma$ is the class of the definitions file (§4.2, p. 15; §5.2, p. 22). The supremum is in `EReal`. Hölder continuity of $\bar\mu$ is the standing assumption of §4–§5 (pp. 12, 20) under which the theorem is proved.
-- source:
--   Denis & Martini, arXiv:math/0607111v1, Theorem 3.1, p. 11, with Γ as defined in §5.2, p. 22

import Mathlib
import Definitions.Def_UncertainPricing_Superrep_Setting
import Definitions.Def_UncertainPricing_Superrep_Compact

namespace UncertainPricing.Superrep

open MeasureTheory Filter Topology BoundedContinuousFunction

theorem theorem_3_1_gamma (T : ℝ) (hT : 0 < T) (μL μU : StieltjesFunction ℝ) (hμL : IsDistFn T μL)
    (hμU : IsDistFn T μU) (Ps : Set (Measure (Ω T)))
    (hPs : ∀ P ∈ Ps, IsMartingaleMeasure P ∧ HypLU μL μU P)
    (hHol : IsHolder T μU) :
    ∃ P'' : Set (Measure (Ω T)), (∀ P ∈ P'', IsMartingaleMeasure P ∧ HypLU μL μU P) ∧
      ∀ f : Ω T →ᵇ ℝ, InGamma Ps μU f → Lam Ps μU f = supE P'' f := by sorry

end UncertainPricing.Superrep
