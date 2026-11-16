-- Prove2me | Theorems.Thm_RGMISFast_conditional_bad_event_weighted_bound
-- name    : RGMISFast.conditional_bad_event_weighted_bound
-- status  : Proved
-- author  : @srikkanthr
-- created : 2026-11-15T23:12:28.111018+00:00
-- url     : https://prove2.me/theorems/c12f2049-fbdf-441c-8a5a-79306fd2a688
-- title:
--   Conditional bad-event bound before averaging the seed rank charges
-- statement:
--   Fix a root-connected candidate $A$, $a=a_m$ with $m\ge1$, a history at $a/2$, and $L\ge8$. Write $\mu$ for its conditional rank law and $E=\{r(v)\ge a\text{ for every }v\in A\}$. Each growth or boundary bad event in Equation (29) has probability at most
--   $$1\{A\text{ active at }a/2\}\int_E e^{-(2S(A,a)+L)}\,d\mu.$$
--   This is the integration step immediately preceding Equation (29), before evaluation of the rank integral. Prove the event vanishes outside the active/high-rank case; condition on the ranks in $A$, apply the appropriate tail from Lemma 6.1 with deterministic threshold $2S(A,a)+L\ge8$, then integrate the prescribed-rank conditional laws. Both the growth event and all boundary indices $i<m$ are included. The statement uses the same explicit history law as Equation (29), for every admissible history. No assumption of the desired gamma-factor bound is made.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, §6.2, proof of Lemma 3.1, paragraph preceding Equation (29), printed p.25 (PDF p.27), manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664.

import Mathlib
import Definitions.Def_RGMISFast_Gamma
import Definitions.Def_RGMISFast_gammaA
import Definitions.Def_RGMISFast_condLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open RGMISFast

theorem RGMISFast.conditional_bad_event_weighted_bound {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (L : ℝ) (hL : 8 ≤ L) (m : ℕ) (hm : 1 ≤ m) (r₀ : V → ℝ)
    (hr₀ : IsHistory r₀ (am m / 2)) (A : Finset V) (hA : IsRootConnected G u A) :
    condLaw r₀ (am m / 2) ∅ (fun _ => 0)
      {r | 2 * S r A (am m) + L < ((GammaAB G r (am m) ((c * am m : ℝ) : WithTop ℝ) A).card : ℝ)} ≤
        (if ActiveAt G r₀ (am m / 2) A then 1 else 0) * (∫⁻ r in {r | ∀ v ∈ A, am m ≤ r v},
          ENNReal.ofReal (Real.exp (-(2 * S r A (am m) + L))) ∂(condLaw r₀ (am m / 2) ∅ (fun _ => 0))) ∧
    ∀ i : ℕ, i < m →
      condLaw r₀ (am m / 2) ∅ (fun _ => 0)
        {r | 32 * c ^ (1 + m - i) * (2 * S r A (am m) + L) < (Kmi G r m i A : ℝ)} ≤
          (if ActiveAt G r₀ (am m / 2) A then 1 else 0) * (∫⁻ r in {r | ∀ v ∈ A, am m ≤ r v},
          ENNReal.ofReal (Real.exp (-(2 * S r A (am m) + L))) ∂(condLaw r₀ (am m / 2) ∅ (fun _ => 0))) := by sorry
