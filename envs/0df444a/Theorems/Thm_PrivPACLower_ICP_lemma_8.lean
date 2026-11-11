-- Prove2me | Theorems.Thm_PrivPACLower_ICP_lemma_8
-- name    : PrivPACLower.ICP.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:47:18.801251+00:00
-- url     : https://prove2.me/theorems/96a22e61-2c0c-4b6e-8157-af6b27870d9f
-- title:
--   Lemma 8 — empirical conversion and confidence amplification
-- statement:
--   Let $H$ be a nonempty binary class and $M$ an $(\varepsilon,\delta)$-DP, $(\alpha,\beta)$-PAC learner using $n\ge1$ examples, where $0<\varepsilon\le1$, $0\le\delta<1$ and $0<\alpha,\beta<1$.
--
--   1. For every $N\ge9n$, there exists an $(\varepsilon,\delta)$-DP mechanism on $N$ examples with empirical error at most $\alpha$ on each $H$-realizable database, except with probability at most $\beta$.
--   2. If $\beta\le1/3$, then for every $\eta\in(0,1)$ and odd integer $T\ge72\ln(1/\eta)$, there exists an $(\varepsilon,\delta)$-DP, $(12\alpha,\eta)$-PAC learner using $Tn$ examples.
--
--   $$\text{sample sizes: }N\ge9n\quad\text{and}\quad Tn,\qquad\text{amplified error: }12\alpha.$$
--
--   Both conclusions are retained in one item. They transfer a PAC guarantee to the empirical setting needed by the packing lower bound.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases, probability measures and extended nonnegative error probabilities; reason: retains replacement adjacency, improper outputs and the joint sample-and-learner experiment; all applied thresholds are nonnegative
--   - reading: a distribution on a bare set with no sigma-algebra specified → a PMF, allowing arbitrary countable support; reason: uses the brief's discrete-law interpretation; on every finite domain this includes all distributions
--   - encoding: PAC accuracy in (0,1), followed by the conclusion (12 alpha, eta)-PAC → the same joint failure inequality also defines PAC for thresholds at least one; reason: expresses the full printed amplification conclusion without adding alpha less than 1/12
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 16, Lemma 8. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Learning
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP

open PrivateUniformGen.Characterization


theorem lemma_8 {X : Type*} {n : ℕ} (H : Set (X → Bool)) (hH : H.Nonempty)
    (hn : 1 ≤ n) (ε δ α β : ℝ) (hε : 0 < ε ∧ ε ≤ 1)
    (hδ : 0 ≤ δ ∧ δ < 1) (hα : 0 < α ∧ α < 1) (hβ : 0 < β ∧ β < 1)
    (M : Learner X n) (hpriv : IsDP M ε δ) (hpac : IsPACLearner H M α β) :
    (∀ N : ℕ, 9*n ≤ N → ∃ A : Learner X N,
      IsDP A ε δ ∧ EmpiricalGuarantee H A α β) ∧
    (β ≤ 1/3 → ∀ (η : ℝ), 0 < η → η < 1 → ∀ T : ℕ, Odd T →
      72*Real.log (1/η) ≤ (T : ℝ) →
      ∃ A : Learner X (T*n), IsDP A ε δ ∧ IsPACLearner H A (12*α) η) := by sorry

end PrivPACLower.ICP
