-- Prove2me | Theorems.Thm_SliceLinearity_Tests_lemma_6_14
-- name    : SliceLinearity.Tests.lemma_6_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:39:33.094076+00:00
-- url     : https://prove2.me/theorems/eca90140-ee78-4f16-9ad3-ff40582cc354
-- title:
--   Lemma 6.14 — the unique size probabilities π₂, π₃, π₄ making λ_{p,k} symmetric; Ber(p) pairwise-independent bits; E|Aᵢ| = 2mp
-- statement:
--   Let $m\ge3$ and $1/m\le p\le1/(m-1)$, and $k=m+1$. There is a unique choice of size probabilities $\pi_2,\pi_3,\pi_4$ for which $\lambda_{p,k}$ is invariant under permuting the $k$ queries. With it, the bits of $\lambda_{p,k}$ are $\mathrm{Ber}(p)$ and pairwise independent, and $\mathbb E[|A_i|]=2mp$.
--
--   The unique choice is the one computed in the proof:
--   $$\pi_2=\tfrac{3-3mp+m(m-1)p^2}{1-p},\qquad\pi_3=\tfrac{2(mp-1)(1-(m-2)p)}{1-p},\qquad\pi_4=\tfrac{(m-3)p(mp-1)}{1-p}.$$
--
--   Differences from the source:
--   - generalization: there is a unique choice of size probabilities π₂, π₃, π₄ for subsets of [m] making λ_{p,k} symmetric → the explicit triple of the proof is admissible and symmetric, and every admissible symmetric triple equals it; reason: this implies the ∃! of the statement; the values are those derived on p. 48
--   - encoding: invariant under permuting the k queries; bits Ber(p) and pairwise independent; E[|Aᵢ|] → ∀ σ v, λ(v ∘ σ) = λ(v); bitProb j 1 = p; PairwiseIndepBits; 2π₂ + 3π₃ + 4π₄; reason: direct transcriptions
--   - encoding: π_a is the probability that an active subset of [m] has size a → Valid includes m < 4 → π₄ = 0, as well as nonnegativity and total mass one; reason: with m ≥ 3 only size four can be impossible; its probability must be zero, so the sampler is a probability distribution even at m = 3
-- source:
--   Aydin, Larsen, Mittal, Richelson, Roy, Low Soundness Linearity Testing on Subsets of the Hypercube, STOC 2027 submission (manuscript sha256 457be236…), §6.2.1, p. 48 (PDF 50), Lemma 6.14; explicit values in its proof, p. 48 (PDF 50)

import Mathlib
import Definitions.Def_SliceLinearity_Tests_ActiveSet

set_option autoImplicit false

namespace SliceLinearity.Tests

/-- **Lemma 6.14** (Size probabilities for the symmetric test), p. 48 (PDF 50), with the explicit
values found in its proof. Let `m ≥ 3` and `1/m ≤ p ≤ 1/(m − 1)`, `k = m + 1`. The size probabilities
`π₂, π₃, π₄` (nonnegative, summing to one, and zero for impossible sizes) for which `λ_{p,k}` is invariant under permuting the `k`
queries exist and are unique, namely `π₂ = (3 − 3mp + m(m−1)p²)/(1−p)`, `π₃ = 2(mp−1)(1−(m−2)p)/(1−p)`,
`π₄ = (m−3)p(mp−1)/(1−p)`. With them, the bits of `λ_{p,k}` are `Ber(p)` and pairwise independent,
and `E[|Aᵢ|] = 2mp`. -/
theorem lemma_6_14 (m : ℕ) (hm : 3 ≤ m) (p : ℝ) (hp1 : 1 / (m : ℝ) ≤ p)
    (hp2 : p ≤ 1 / ((m : ℝ) - 1)) :
    let Valid : ℝ → ℝ → ℝ → Prop := fun π2 π3 π4 =>
      0 ≤ π2 ∧ 0 ≤ π3 ∧ 0 ≤ π4 ∧ π2 + π3 + π4 = 1 ∧ (m < 4 → π4 = 0)
    let Symm : ℝ → ℝ → ℝ → Prop := fun π2 π3 π4 =>
      ∀ (σ : Equiv.Perm (Fin (m + 1))) (v : Fin (m + 1) → ZMod 2),
        symActiveLaw p m π2 π3 π4 (v ∘ σ) = symActiveLaw p m π2 π3 π4 v
    (Valid (piTwo p m) (piThree p m) (piFour p m) ∧ Symm (piTwo p m) (piThree p m) (piFour p m) ∧
      ∀ π2 π3 π4 : ℝ, Valid π2 π3 π4 → Symm π2 π3 π4 →
        π2 = piTwo p m ∧ π3 = piThree p m ∧ π4 = piFour p m) ∧
    (∀ j, bitProb (lambdaPK p m) j 1 = p) ∧ PairwiseIndepBits (lambdaPK p m) ∧
    2 * piTwo p m + 3 * piThree p m + 4 * piFour p m = 2 * (m : ℝ) * p := by sorry

end SliceLinearity.Tests
