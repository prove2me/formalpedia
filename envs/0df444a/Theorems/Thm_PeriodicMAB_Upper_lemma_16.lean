-- Prove2me | Theorems.Thm_PeriodicMAB_Upper_lemma_16
-- name    : PeriodicMAB.Upper.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:50.155713+00:00
-- url     : https://prove2.me/theorems/54e07542-641b-474f-8edc-0148c0c562a2
-- title:
--   Lemma 16, p. 43 — $\sum_{t\in\Psi^{(s)}(T)}\tilde w^{(s)}_{\tilde\pi_t,t}\le4\sigma\sqrt{|\Psi^{(s)}(T)|\,d\log(8T/\delta)\log(T/d)}$
-- statement:
--   Assume Assumption 3, $nK\le T$, positive periods $T_1,\dots,T_K$ with $d=\sum_kT_k$, and $\delta\in(0,1)$. For the weak oracle and every round $s\in\mathcal S=\{1,\dots,\lfloor\log_2T\rfloor\}$,
--   $$
--   \sum_{t\in\Psi^{(s)}(T)}\tilde w^{(s)}_{\tilde\pi_t,t}\le4\sigma\sqrt{|\Psi^{(s)}(T)|\,d\,\log\Big(\frac{8T}{\delta}\Big)\log\Big(\frac Td\Big)} ,
--   $$
--   where $\Psi^{(s)}(T)$ is the set of stage-two epochs before $T$ at which the oracle pulled an arm in Step 9 of round $s$, and $\tilde w^{(s)}_{\tilde\pi_t,t}$ is the width (17) of the arm pulled at $t$.
--
--   This bounds the total exploration cost of round $s$, which the proof of Lemma 11 converts into regret.
--
--   **Formalization Note** The statement is pathwise and holds for every reward table (the oracle's run depends on the rewards only through which arms it pulls). Assumption 3 enters through $T_k<n/2$, which makes every stage-one phase count at least $2$, and through $d<T$.
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, p. 43, Lemma 16

import Mathlib
import Definitions.Def_PeriodicMAB_Upper_Model
import Definitions.Def_PeriodicMAB_Upper_Spectral
import Definitions.Def_PeriodicMAB_Upper_Policy

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace PeriodicMAB.Upper

/-- Lemma 16 (p. 43): for the oracle policy (any reward table `Y`) and every round `s ∈ 𝒮`,
`∑_{t ∈ Ψ^(s)(T)} w̃^(s)_{π̃_t,t} ≤ 4σ √(|Ψ^(s)(T)| d log(8T/δ) log(T/d))`, `d = ∑_k T_k`. -/
theorem lemma_16 (σ : ℝ≥0) (hσ : 0 < σ) {K : ℕ} [NeZero K] (Tper : Fin K → ℕ) (T n g : ℕ)
    (δ : ℝ) (hTper : ∀ k, 0 < Tper k) (hA3 : Assumption3 T n g Tper) (hnK : n * K ≤ T)
    (hδ : 0 < δ) (hδ1 : δ < 1) (Y : Fin K → ℕ → ℝ) :
    ∀ s ∈ Icc 1 (Nat.log 2 T),
      ∑ t ∈ psiAt σ δ T n Tper Y s T, wAt σ δ T n Tper Y s (policy σ δ T n Tper Y t) t ≤
        4 * σ * Real.sqrt ((psiAt σ δ T n Tper Y s T).card * effArms Tper *
          Real.log (8 * T / δ) * Real.log (T / effArms Tper)) := by sorry

end PeriodicMAB.Upper
