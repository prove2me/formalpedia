-- Prove2me | Theorems.Thm_SecSampling_Supplement_theorem_6
-- name    : SecSampling.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:03:03.519679+00:00
-- url     : https://prove2.me/theorems/1a8441da-7564-5fc8-ac3e-cfb2e8570936
-- title:
--   Theorem 6 — no AOSp algorithm ignorant of both $p$ and $n$ has a positive guarantee
-- statement:
--   Let $A$ be any ordinal, possibly randomized AOSp algorithm whose decisions do not depend on the instance size $n$. The algorithm is fixed before the sampling probability is chosen. Then, for every $\varepsilon>0$, there exist $p\in(0,1)$, a size $n$, distinct values, and a valid adversarial order of the online elements such that
--   $$
--   \Pr[A\text{ selects the maximum online value}]<\varepsilon.
--   $$
--
--   Hence an algorithm that knows neither $p$ nor $n$ has success guarantee zero.
--
--   **Formalization Note** The algorithm may use the sample count and the complete ordinal rank history and may randomize behaviorally. Quantifying it before $p$ enforces ignorance of $p$; equality of its decisions across its first argument enforces ignorance of $n$. The sampled-set-dependent order is required to list every online element exactly once.
--
--   Differences from the source:
--   - encoding: no positive success guarantee when $p$ and $n$ are unknown → for every $\varepsilon>0$ some $p\in(0,1)$, size, injective values and valid online order give success below $\varepsilon$; reason: this is exactly the epsilon characterization of a zero worst-case guarantee
--   - encoding: an ordinal randomized algorithm knows neither parameter → a behavioral ordinal algorithm quantified before $p$ and invariant in its explicit size argument; reason: the quantifier order and invariance express precisely the unavailable information
-- source:
--   Correa, Cristi, Feuilloley, Oosterwijk & Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, Theorem 6 and §7.2, p.38 (PDF p.39)

import Definitions.Def_SecSampling_AOSp

open Set

namespace SecSampling.Supplement

/-- **Theorem 6** (Correa et al., arXiv:2011.07869v1, §7.2, p.38, PDF p.39). An ordinal,
possibly randomized AOSp algorithm that knows neither the sampling probability `p` nor the size
`n` has zero success guarantee: for every positive epsilon an adversary can choose
`p ∈ (0,1)`, a size, distinct values and a valid sample-dependent online order on which its win
probability is below epsilon.

**Formalization Note.** The algorithm is quantified before `p` and `n`, so it cannot depend on
either. The displayed invariance in the first argument says exactly that it ignores `n`; it may
still use the sample count and complete ordinal history, and may randomize behaviourally. The
conclusion is the epsilon form of a zero infimum and includes every standing assumption of AOSp,
including injective values and a valid adversarial online order. -/
theorem theorem_6 :
    ∀ A : SecSampling.Algorithm,
      SecSampling.IsAlgorithm A →
      (∀ (n n' s : ℕ) (h : List (ℕ × ℕ)), A n s h = A n' s h) →
      ∀ ε : ℝ, 0 < ε →
        ∃ p : ℝ, p ∈ Ioo (0 : ℝ) 1 ∧
          ∃ (n : ℕ) (v : Fin n → ℝ) (ord : Finset (Fin n) → List (Fin n)),
            Function.Injective v ∧ SecSampling.IsOnlineOrder ord ∧
              SecSampling.winProb p A v ord < ε := by sorry

end SecSampling.Supplement
