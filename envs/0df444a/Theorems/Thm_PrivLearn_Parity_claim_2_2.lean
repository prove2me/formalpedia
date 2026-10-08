-- Prove2me | Theorems.Thm_PrivLearn_Parity_claim_2_2
-- name    : PrivLearn.Parity.claim_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:30.604948+00:00
-- url     : https://prove2.me/theorems/15a98328-aa17-4c0d-b83c-8afa8acf1414
-- title:
--   Claim 2.2 — composition and post-processing of differentially private algorithms
-- statement:
--   Let $A_1,\dots,A_k$ be randomized algorithms on databases in $D^n$, where $A_i$ is $\varepsilon_i$-differentially private, and let $g$ be a probabilistic algorithm applied to their results. Run the $A_i$ on the same database with independent coins and output $g(A_1(z),\dots,A_k(z))$. Then this algorithm is
--
--   $$
--   \Big(\sum_{i=1}^k \varepsilon_i\Big)\text{-differentially private.}
--   $$
--
--   Composition and post-processing are the two closure properties used to build private algorithms from private pieces; Lemma 4.5 applies them to the amplified learner.
--
--   **Formalization Note** The output of $A_i$ on $z$ is a probability measure $A_i(z)$ on a measurable space $O_i$; independence of the coins makes the joint law the product measure $\bigotimes_i A_i(z)$; the probabilistic algorithm $g$ is a Markov kernel from $\prod_i O_i$ to the output space, and the output law is the product measure bound to $g$.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 8, Claim 2.2

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy

open MeasureTheory ProbabilityTheory

namespace PrivLearn.Parity

/-- Claim 2.2 (Composition and Post-processing), p. 8. If the algorithms `A_1, …, A_k` are
`ε_i`-differentially private and run on the same database with independent coins, and `g` is a
probabilistic algorithm (a Markov kernel) applied to their results, then the algorithm
`z ↦ g(A_1(z), …, A_k(z))` is `(∑ ε_i)`-differentially private. -/
theorem claim_2_2 {D : Type*} {n k : ℕ} {O : Fin k → Type*} [∀ i, MeasurableSpace (O i)]
    {O' : Type*} [MeasurableSpace O'] (A : ∀ i, (Fin n → D) → Measure (O i))
    [∀ i z, IsProbabilityMeasure (A i z)] (ε : Fin k → ℝ) (hA : ∀ i, PrivLearn.Generic.IsDP (A i) (ε i))
    (g : Kernel (∀ i, O i) O') [IsMarkovKernel g] :
    PrivLearn.Generic.IsDP (fun z => (Measure.pi fun i => A i z).bind g) (∑ i, ε i) := by sorry

end PrivLearn.Parity
