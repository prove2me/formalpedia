-- Prove2me | Theorems.Thm_UnknownProphet_NoSamples_coupling
-- name    : UnknownProphet.NoSamples.coupling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:49.97895+00:00
-- url     : https://prove2.me/theorems/5cf9a797-d0e5-4520-9134-f0c5b6e422ef
-- title:
--   Proof of Theorem 2, p. 8 — pointwise coupling display before (5)
-- statement:
--   Fix a zero-sample rule $r$ that is $\varepsilon$ value oblivious on an infinite set $V$ with constants $q_i\in[0,1]$, where $\varepsilon>0$. For any distinct observations $s_1,\ldots,s_n\in V$, let $\hat r$ stop on a record at time $i$ with probability $q_i$. Conditional on that observation sequence, the probability of selecting its maximum obeys
--
--   $$
--   \Pr_r(X_\tau=X_{(n)}\mid X=s)\le\Pr_{\hat r}(X_{\hat\tau}=X_{(n)}\mid X=s)+n\varepsilon.
--   $$
--
--   This transfers success bounds from the coupled record rule to an approximately value-oblivious rule.
--
--   **Formalization Note** Indices are zero-based. The Lean probability is the finite sum of conditional stopping probabilities at positions holding the maximum; distinctness makes that position unique.
-- source:
--   Correa, Dütting, Fischer & Schewior, Prophet Inequalities for I.I.D. Random Variables from an Unknown Distribution, arXiv:1811.06114v2, p. 8, proof of Theorem 2, pointwise display before (5)

import Mathlib
import Definitions.Def_UnknownProphet_NoSamples_Model

namespace UnknownProphet.NoSamples

/-- Pointwise coupling bound before equation (5), p. 8. -/
theorem coupling (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (R : StoppingRule 0 n) (V : Set ℕ) (q : Fin n → ℝ)
    (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (h : ValueObliviousWith ε R V q)
    (s : Fin n → ℕ) (hs : ∀ j, s j ∈ V) (hinj : Function.Injective s) :
    pickMaxProb R (fun j => (s j : ℝ)) ≤
      pickMaxProb (hatRule q hq) (fun j => (s j : ℝ)) + n * ε := by sorry

end UnknownProphet.NoSamples
