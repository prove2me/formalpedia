-- Prove2me | Theorems.Thm_StochAutoreg_lemma_4_1
-- name    : StochAutoreg.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:18:03.464279+00:00
-- url     : https://prove2.me/theorems/26fd70da-f05b-4149-917f-3c23432641bc
-- title:
--   Lemma 4.1 — aggregation of a finite list of predictors under forward KL
-- statement:
--   Let $P$ be a prompt law, $p_\star:\Sigma^\star\to[0,1]$, $X\sim P$ and $Y\mid X\sim\mathrm{Bern}(p_\star(X))$. For integers $K,T\ge1$ and predictors $q_1,\dots,q_K:\Sigma^\star\to[0,1]$, one learner, using the list but neither $P$ nor $p_\star$, outputs from $T$ independent copies of $(X,Y)$ a predictor $\bar q$ with
--
--   $$\mathbb E\bigl[\mathbb E_{X\sim P}\mathrm{KL}(p_\star(X)\|\bar q(X))\bigr]\le\min_{j\in[K]}\mathbb E_{X\sim P}\mathrm{KL}(p_\star(X)\|q_j(X))+\frac{\log(K+1)}{T},$$
--
--   the outer expectation being over the samples and the learner's randomness. This is the upper-bound tool for the finite classes and for the base complexity of the combined class.
--
--   Differences from the source:
--   - encoding: if q₁, …, q_K are random and independent of the samples, the bound holds conditional on their realized values → the statement holds for every realized list q; reason: conditioning on an independent list reduces to a fixed list
--   - encoding: the expectations and the minimum of (4.1) → a lintegral and a tsum in ℝ≥0∞, and ⨅ over Fin K; reason: the same quantities, with +∞ kept; Fin K is finite and nonempty, so ⨅ is the minimum
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Lemma 4.1, Eq. (4.1), p.10

import Mathlib
import Definitions.Def_StochAutoreg_risk
import Definitions.Def_StochAutoreg_Learner
import Definitions.Def_StochAutoreg_iidSeedMeasure
import Definitions.Def_StochAutoreg_labelLaw
import Definitions.Def_StochAutoreg_promptMeasurableSpace
open MeasureTheory

namespace StochAutoreg

/-- **Lemma 4.1** (aggregation of a finite list). For `K, T ≥ 1` and predictors `q₁, …, q_K`, `T` independent copies of
`(X, Y)` suffice to output `q̄` with
`E[E_{X∼P} KL(p⋆(X)‖q̄(X))] ≤ min_j E_{X∼P} KL(p⋆(X)‖q_j(X)) + log(K+1)/T`, Eq. (4.1).
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, Lemma 4.1, p.10.

**Formalization Note.** The learner is fixed before `P` and `p⋆`. The statement holds for each realized list `q`,
which covers the paper's closing sentence on random lists independent of the sample. -/
theorem lemma_4_1 (K T : ℕ) (hK : 1 ≤ K) (hT : 1 ≤ T) (q : Fin K → List Bool → unitInterval) :
    ∃ A : Learner (List Bool × Bool) T,
      ∀ (P : PMF (List Bool)) (pstar : List Bool → unitInterval),
        ∫⁻ w, risk P (fun x => (pstar x : ℝ)) (A.run w.1 w.2) ∂iidSeedMeasure (labelLaw P pstar) T ≤
          (⨅ j, risk P (fun x => (pstar x : ℝ)) (q j)) +
            ENNReal.ofReal (Real.log ((K : ℝ) + 1) / (T : ℝ)) := by sorry

end StochAutoreg
