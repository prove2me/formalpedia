-- Prove2me | Theorems.Thm_TsitsiklisGittins_IndexTheorem_index_antitone
-- name    : TsitsiklisGittins.IndexTheorem.index_antitone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:31.272424+00:00
-- url     : https://prove2.me/theorems/5943b8e1-48e5-4b55-a493-6d7e438d7d9c
-- title:
--   Index monotonicity — along a run of the index algorithm, γ(s*) ≥ γ(q*) for consecutive picks s*, q*
-- statement:
--   Consider the semi-Markov multi-armed bandit problem with finite nonempty state spaces and a run $s_0,s_1,\dots$ of the index algorithm with indices $\gamma$. Then for every $k$ with $s_{k+1}$ defined,
--   $$
--   \gamma(s_{k+1})\le\gamma(s_k).
--   $$
--   For $k=0$ this is the claim that if $s^*$ is the first state picked and $q^*$ the next one, then $\gamma(s^*)\ge\gamma(q^*)$: if $q^*$ is in the bandit of $s^*$, $\gamma(q^*)=\hat r(q^*)\le\max_x r(x)=\gamma(s^*)$ by (2.3), and otherwise $\gamma(q^*)=r(q^*)\le r(s^*)=\gamma(s^*)$.
--
--   The indices are thus non-increasing in the picking order, which is the first half of the characterization "x can be picked before y if and only if $\gamma(x)\ge\gamma(y)$".
--
--   **Formalization Note** The page proves the case of the first two picks and invokes "the recursive nature of the algorithm" for the rest; the Lean statement is the resulting claim for every pair of consecutive picks.
-- source:
--   Tsitsiklis, A Short Proof of the Gittins Index Theorem, Ann. Appl. Probab. 4 (1994), p. 198 (PDF p. 5), Section 2, proof of Theorem 2.2

import Mathlib
import Definitions.Def_TsitsiklisGittins_IndexTheorem_IndexRun

namespace TsitsiklisGittins.IndexTheorem

/-- Proof of Theorem 2.2 of Tsitsiklis (1994), p. 198: along a run of the index algorithm the
indices do not increase; a state picked next never has a larger index than the state picked
before it, `γ(s*) ≥ γ(q*)`. -/
theorem index_antitone {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (B : SemiMarkovBandit n X)
    (seq : List (Σ i, X i)) (γ : (Σ i, X i) → ℝ) (hrun : B.IsIndexRun seq γ)
    (k : ℕ) (hk : k + 1 < seq.length) :
    γ seq[k + 1] ≤ γ seq[k] := by sorry

end TsitsiklisGittins.IndexTheorem
