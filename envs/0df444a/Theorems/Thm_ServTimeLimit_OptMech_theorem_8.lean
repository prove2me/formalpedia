-- Prove2me | Theorems.Thm_ServTimeLimit_OptMech_theorem_8
-- name    : ServTimeLimit.OptMech.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:52.681379+00:00
-- url     : https://prove2.me/theorems/81dfb500-f827-4b55-a6d2-6baf14f22d37
-- title:
--   Theorem 8, p. 19 — the revenue-optimal IC and IR mechanism assigns Theorem 1's first-best time, extracts all surplus and achieves the first best
-- statement:
--   Assume $\Lambda, c, \bar\theta > 0$, and let $\Lambda_1, \Lambda_2, \widetilde T$ be the constants of Theorem 1. In each congestion regime take the first-best admitted set $\Phi$ and time function $t$ of Theorem 1:
--
--   - if $\Lambda \le \Lambda_1$: $\Phi = [\theta_l, \bar\theta]$ and $t(\theta) = \theta$, for some $\theta_l \in [0,\bar\theta]$;
--   - if $\Lambda_1 \le \Lambda \le \Lambda_2$: $\Phi = [\theta_l, \bar\theta]$ and $t(\theta) = \min\{\theta, T\}$, for some $0 \le \theta_l \le T \le \bar\theta$;
--   - if $\Lambda \ge \Lambda_2$: $\Phi = [\widetilde T, 2\widetilde T]$ and $t(\theta) = \widetilde T$;
--
--   and set the price
--   $$p(\theta) = \min\{\theta, t(\theta)\} - c\,W(\Phi, t).$$
--   Then, in each regime (with $\theta_l$, respectively $(\theta_l, T)$, suitably chosen):
--
--   1. $(\Phi, t)$ is a first-best allocation;
--   2. $(\Phi, t, p)$ is a direct mechanism (in particular $p \ge 0$ on $\Phi$) that is incentive compatible and individually rational;
--   3. a type $\theta \in [0,\bar\theta]\setminus\Phi$ that is not admitted gains nothing by claiming an admitted type: $\min\{t(\theta'),\theta\} - p(\theta') - cW \le 0$ for $\theta' \in \Phi$;
--   4. its revenue is the largest among all IC and IR direct mechanisms: $\pi(\Phi', p') \le \pi(\Phi, p)$ for every IC and IR mechanism $(\Phi', t', p')$;
--   5. it achieves the first best: $\pi(\Phi, p) = SW(\Phi, t)$.
--
--   In words: even though the firm may use any time function and any price, the revenue-maximising mechanism mimics the first best, including its time limit when congestion is high, and extracts all consumer surplus.
--
--   **Formalization Note** "According to Theorem 1" is made explicit by one clause per case of Theorem 1, with that case's admitted set and time function. "The optimal direct mechanism" is read as clauses 2 and 4; no uniqueness of the optimal mechanism is claimed, as the page does not claim it. The program on p. 19 requires $p:\Phi \to \mathbb R_+$, so clause 2 includes $p \ge 0$, which the paper's proof does not check. Clause 3 is the proof's "either if she gets to use the system or not".
-- source:
--   Feldman & Segev, The Important Role of Time Limits when Consumers Choose their Time in Service, SSRN 3424317 (version of 2021-10-07), p. 19, Theorem 8 (with Theorem 1, pp. 8–9)

import Mathlib
import Definitions.Def_ServTimeLimit_OptMech_Model

namespace ServTimeLimit.OptMech

open MeasureTheory

/-- Theorem 8 (p. 19), with the first-best time function of Theorem 1 (pp. 8–9) in each of its
three regimes. For the regime's admitted set `Φ`, time function `t` and the full-extraction price
`p(θ) = min{θ, t(θ)} − c W`: (i) `(Φ, t)` is first-best; (ii) `(Φ, t, p)` is a feasible, IC and IR
direct mechanism; (iii) a non-admitted type gains nothing by claiming an admitted type;
(iv) `(Φ, t, p)` has the largest revenue among all feasible IC and IR mechanisms; (v) its revenue
equals the first-best welfare. -/
theorem theorem_8 (P : Params) (hP : P.Standing) :
    -- case Λ ≤ Λ₁: admit [θ_l, θ̄], t(θ) = θ
    (P.Lam ≤ lam1 P →
      ∃ θl : ℝ, 0 ≤ θl ∧ θl ≤ P.θbar ∧
        ∀ (Φ : Set ℝ) (t p : ℝ → ℝ), Φ = Set.Icc θl P.θbar → t = (fun θ => θ) →
          (∀ θ, p θ = min θ (t θ) - P.c * waitTime P Φ t) →
          IsFirstBest P Φ t ∧
          (IsMechanism P Φ t p ∧ IsIC Φ t p ∧ IsIR P Φ t p) ∧
          (∀ θ ∈ Set.Icc 0 P.θbar \ Φ, ∀ θ'' ∈ Φ,
            min (t θ'') θ - p θ'' - P.c * waitTime P Φ t ≤ 0) ∧
          (∀ (Φ' : Set ℝ) (t' p' : ℝ → ℝ), IsMechanism P Φ' t' p' → IsIC Φ' t' p' →
            IsIR P Φ' t' p' → revenue P Φ' p' ≤ revenue P Φ p) ∧
          revenue P Φ p = welfare P Φ t) ∧
    -- case Λ₁ ≤ Λ ≤ Λ₂: admit [θ_l, θ̄], time limit t(θ) = min{θ, T}
    (lam1 P ≤ P.Lam → P.Lam ≤ lam2 P →
      ∃ θl T : ℝ, 0 ≤ θl ∧ θl ≤ T ∧ T ≤ P.θbar ∧
        ∀ (Φ : Set ℝ) (t p : ℝ → ℝ), Φ = Set.Icc θl P.θbar → t = (fun θ => min θ T) →
          (∀ θ, p θ = min θ (t θ) - P.c * waitTime P Φ t) →
          IsFirstBest P Φ t ∧
          (IsMechanism P Φ t p ∧ IsIC Φ t p ∧ IsIR P Φ t p) ∧
          (∀ θ ∈ Set.Icc 0 P.θbar \ Φ, ∀ θ'' ∈ Φ,
            min (t θ'') θ - p θ'' - P.c * waitTime P Φ t ≤ 0) ∧
          (∀ (Φ' : Set ℝ) (t' p' : ℝ → ℝ), IsMechanism P Φ' t' p' → IsIC Φ' t' p' →
            IsIR P Φ' t' p' → revenue P Φ' p' ≤ revenue P Φ p) ∧
          revenue P Φ p = welfare P Φ t) ∧
    -- case Λ ≥ Λ₂: admit [T̃, 2T̃], t(θ) = T̃
    (lam2 P ≤ P.Lam →
        ∀ (Φ : Set ℝ) (t p : ℝ → ℝ), Φ = Set.Icc (Ttilde P) (2 * Ttilde P) →
          t = (fun _ => Ttilde P) →
          (∀ θ, p θ = min θ (t θ) - P.c * waitTime P Φ t) →
          IsFirstBest P Φ t ∧
          (IsMechanism P Φ t p ∧ IsIC Φ t p ∧ IsIR P Φ t p) ∧
          (∀ θ ∈ Set.Icc 0 P.θbar \ Φ, ∀ θ'' ∈ Φ,
            min (t θ'') θ - p θ'' - P.c * waitTime P Φ t ≤ 0) ∧
          (∀ (Φ' : Set ℝ) (t' p' : ℝ → ℝ), IsMechanism P Φ' t' p' → IsIC Φ' t' p' →
            IsIR P Φ' t' p' → revenue P Φ' p' ≤ revenue P Φ p) ∧
          revenue P Φ p = welfare P Φ t) := by sorry

end ServTimeLimit.OptMech
