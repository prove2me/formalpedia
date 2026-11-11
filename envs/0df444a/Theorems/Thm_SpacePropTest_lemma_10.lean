-- Prove2me | Theorems.Thm_SpacePropTest_lemma_10
-- name    : SpacePropTest.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:55:43.934934+00:00
-- url     : https://prove2.me/theorems/9ca04728-72fd-4286-aee6-fef876d6e6a0
-- title:
--   Lemma 10, p.16 — $1/(10M)$-indistinguishable $M$-state chains with a common start state have $\hat p_{C_1}(s)\le1.5\,\hat p_{C_2}(s)$
-- statement:
--   Let $C_1,C_2$ be Markov chains on the same set of $M$ states with the same start state, and suppose they are $\frac1{10M}$-indistinguishable. Then for every state $s$,
--
--   $$\hat p_{C_1}(s)\le1.5\,\hat p_{C_2}(s).$$
--
--   This is the bridge from transition-level closeness to acceptance-level closeness in every lower bound of the paper.
--
--   Differences from the source:
--   - encoding: two $M$-state Markov chains with the same start state → two stochastic matrices on a common finite state type $\sigma$ with $M=|\sigma|$ and a common start state; reason: the same objects
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Lemma 10, p.16 (PDF 18); proof, pp.53–54 (PDF 55–56)

import Mathlib
import Definitions.Def_SpacePropTest_MarkovChain
import Definitions.Def_SpacePropTest_Indist

set_option autoImplicit false

namespace SpacePropTest

/-- **Lemma 10** (C. Canonne, X. Chen, W. Pires, T. Pitassi, R. A. Servedio, *The Space Complexity
of Property Testing*, manuscript of November 2, 2026, sha256 65850aa6…; p.16 (PDF 18), proof
pp.53–54 (PDF 55–56)). Let `C₁, C₂` be two `M`-state Markov chains with the same start state that
are `1/(10M)`-indistinguishable. Then for every state `s`, `p̂_{C₁}(s) ≤ 1.5 p̂_{C₂}(s)`.

**Formalization Note.** The chains are stochastic matrices on a common finite state type `σ`
with `M = |σ|` and a common start state `s₀`. -/
theorem lemma_10 {σ : Type*} [Fintype σ] [DecidableEq σ] (C₁ C₂ : Matrix σ σ ℝ)
    (h₁ : IsStochastic C₁) (h₂ : IsStochastic C₂) (s₀ : σ)
    (hind : Indist C₁ C₂ (1 / (10 * Fintype.card σ))) (s : σ) :
    longRun C₁ s₀ s ≤ 1.5 * longRun C₂ s₀ s := by sorry

end SpacePropTest
