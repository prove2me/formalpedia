-- Prove2me | Theorems.Thm_PrivPACLower_ICP_lemma_7
-- name    : PrivPACLower.ICP.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:48:04.894299+00:00
-- url     : https://prove2.me/theorems/dd85ff0a-e928-4436-9b64-a2361f1f576c
-- title:
--   Lemma 7 — strict error comparison for independently packed hard blocks
-- statement:
--   Assume the parameters, classes and maps of Lemma 6, now with every component domain finite. Let $Q,N$ be positive integers such that $Q\le N$ and $Q\le\sum_i(s_i-1)_+$. If $Q<N$, assume that the packing has a padding point. Let $\gamma,\eta\in[0,1]$. If an $(\varepsilon,\delta)$-DP algorithm on $N$ examples has empirical error at most $\gamma$ with probability at least $1-\eta$ on every $H$-realizable database, then
--
--   $$\left(\frac{\alpha_0}{8e}-\eta\right)Q<\gamma N.$$
--
--   This strict inequality compares the total forced errors on hard blocks with a guarantee for the entire database; equality does not suffice.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases, probability measures and extended nonnegative error probabilities; reason: retains replacement adjacency, improper outputs and the joint sample-and-learner experiment; all applied thresholds are nonnegative
--   - encoding: least sample size, possibly nonexistent → sInf in Nat-infinity with its infinity-preserving coercion into ENNReal; reason: unlearnable classes have infinite cost, zero-sample singleton classes retain cost zero, and infinite suprema are not replaced by zero
--   - generalization: privacy for every hypothesis-output event → privacy for product-measurable hypothesis-output events; reason: all empirical-error events and finite component restriction events are measurable, so the lower bound applies under the weaker privacy hypothesis
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 15, Lemma 7. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Packing
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP

open PrivateUniformGen.Characterization


theorem lemma_7 {X : Type*} {k : ℕ} {Y : Fin k → Type*} [∀ i, Fintype (Y i)]
    (H : Set (X → Bool)) (Gs : ∀ i, Set (Y i → Bool)) (Φ : ∀ i, Y i → X)
    (hp : PackingVia H Gs Φ) (ε δ α₀ : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1) (hα₀ : 0 < α₀ ∧ α₀ ≤ 1/4)
    (hδ : 0 ≤ δ ∧ δ ≤ α₀/8) (Q N : ℕ) (hQ : 1 ≤ Q) (hN : 1 ≤ N)
    (hQN : Q ≤ N) (hcost : (Q : ℕ∞) ≤ blockCost Gs ε δ α₀)
    (hpad : Q < N → ∃ z : X × Bool, PaddingPoint H Gs Φ z)
    (γ η : ℝ) (hγ : 0 ≤ γ ∧ γ ≤ 1) (hη : 0 ≤ η ∧ η ≤ 1)
    (M : Learner X N) (hpriv : IsDP M ε δ) (hacc : EmpiricalGuarantee H M γ η) :
    (α₀/(8*Real.exp 1) - η)*(Q : ℝ) < γ*(N : ℝ) := by sorry

end PrivPACLower.ICP
