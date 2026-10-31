-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P14_entropy_splitting
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P14.entropy_splitting
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:21:00.648345+00:00
-- url     : https://prove2.me/theorems/f9ae1bc4-25ac-4d81-94ca-2682b9fcb5b7
-- title:
--   Entropy splitting for a finite list
-- statement:
--   Let $m\ge1$, let $X_1,\ldots,X_m,Z$ be finite random variables, and let $\varepsilon\ge0$ and $\alpha\in\mathbb R$. Conditional min-entropy is the negative binary logarithm of the average guessing probability $\sum_z\max_x P_{XZ}(x,z)$. Smoothing deletes an event of probability at most $\varepsilon$, without renormalization. Suppose every distinct pair satisfies $H_{\min}^{\varepsilon}(X_iX_j\mid Z)\ge\alpha$. There exists a random index $V\in\{1,\ldots,m\}$ such that every independent index $W$ with $H_{\min}(W)\ge1$ satisfies
--
--   $$H_{\min}^{2m\varepsilon}(X_W\mid V,W,Z,\ V\ne W)\ge\frac\alpha2-\log_2m-1.$$
--
--   Here $W$ is independent of the whole original tuple and of $V$. Different alphabets for the $X_i$ are allowed using a tagged union; $W$ in the condition supplies its tag. The conditioning event has probability at least $1/2$. Smoothing levels above one are permitted, with zero retained mass corresponding to entropy $+\infty$. The Lean formula uses the exactly equivalent exponential guessing-probability bounds.
-- source:
--   Secure Identification and QKD in the Bounded-Quantum-Storage Model, arXiv:0708.2557v3, PDF p. 7, Lemma2.2: Entropy-Splitting Lemma

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P14

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

open QAlgorithms.Papers.Independent.Gap48.P11 (blockMatrix cqDistance)

open QAlgorithms.Papers.Independent.Claimed50.P31 (bb84Vector)

open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Positive list length and inhabited fibers supply the tagged union's inhabitant.
This derived instance adds no hypothesis to Lemma 2.2. -/
local instance {m : ℕ} [NeZero m] {A : Fin m → Type*}
    [∀ i, Nonempty (A i)] : Nonempty (Sigma A) :=
  ⟨⟨0, Classical.choice (inferInstance : Nonempty (A 0))⟩⟩

/-- PDF p.7, Lemma 2.2, with its construction and proof on pp.21-22.
V is chosen before the independent W. The entropy inequalities are written
as equivalent bounds on retained average guessing probabilities. -/
theorem entropy_splitting
    (m : ℕ) [NeZero m]
    {S : Type} {Z : Type*} [Fintype S] [Nonempty S] [Fintype Z] [Nonempty Z]
    {A : Fin m → Type*} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (p : Law S) (X : (i : Fin m) → S → A i) (z : S → Z)
    (alpha epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hpair : ∀ i j : Fin m, i ≠ j →
      smoothGuess p.prob (fun s => (X i s, X j s)) z epsilon ≤
        Real.rpow 2 (-alpha)) :
    ∃ V : S → Fin m, ∀ W : Law (Fin m),
      (∀ i, W.prob i ≤ 1 / 2) →
      smoothGuess
        (conditionMass (fun sw : S × Fin m => p.prob sw.1 * W.prob sw.2)
          (fun sw => V sw.1 ≠ sw.2))
        (fun sw : S × Fin m => (⟨sw.2, X sw.2 sw.1⟩ : Sigma A))
        (fun sw : S × Fin m => ((V sw.1, sw.2), z sw.1))
        (2 * (m : ℝ) * epsilon) ≤
          Real.rpow 2 (-(alpha / 2 - Real.logb 2 m - 1)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P14

end
