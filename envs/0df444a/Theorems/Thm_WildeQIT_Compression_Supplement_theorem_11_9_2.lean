-- Prove2me | Theorems.Thm_WildeQIT_Compression_Supplement_theorem_11_9_2
-- name    : WildeQIT.Compression.Supplement.theorem_11_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T04:14:17.31534+00:00
-- url     : https://prove2.me/theorems/19c348f3-1db9-5665-aa78-a8559fc2389c
-- title:
--   Theorem 11.9.2: equivalence of monotonicity, joint convexity, strong subadditivity and concavity of conditional entropy
-- statement:
--   The following five statements are equivalent.
--
--   1. The quantum relative entropy is monotone under quantum channels: $D(\rho\|\sigma)\ge D(\mathcal N(\rho)\|\mathcal N(\sigma))$ for all $\rho,\sigma\in\mathcal D(\mathcal H)$ and every channel $\mathcal N:\mathcal L(\mathcal H)\to\mathcal L(\mathcal H')$.
--   2. It is monotone under partial trace: $D(\rho_{AB}\|\sigma_{AB})\ge D(\rho_B\|\sigma_B)$ for all $\rho_{AB},\sigma_{AB}\in\mathcal D(\mathcal H_A\otimes\mathcal H_B)$.
--   3. It is jointly convex: $\sum_xp_X(x)D(\rho_x\|\sigma_x)\ge D(\rho\|\sigma)$ for every probability distribution $p_X$ on a finite alphabet, all $\rho_x,\sigma_x\in\mathcal D(\mathcal H)$, $\rho=\sum_xp_X(x)\rho_x$ and $\sigma=\sum_xp_X(x)\sigma_x$.
--   4. The conditional quantum mutual information is non-negative: $I(A;B|C)_\rho\ge0$ for every $\rho_{ABC}$.
--   5. The conditional quantum entropy is concave: $H(A|B)_\rho\ge\sum_xp_X(x)H(A|B)_{\rho_x}$ for every finite ensemble $\{p_X(x),\rho^x_{AB}\}$ with $\rho_{AB}=\sum_xp_X(x)\rho^x_{AB}$.
--
--   Each statement quantifies over all finite-dimensional systems, states, channels and ensembles. The theorem shows that the fundamental entropy inequalities of the chapter are one fact in five forms.
--
--   **Formalization Note** The equivalence is `List.TFAE` of five closed propositions, each quantified over all finite index types. In statement 3 the weights multiply relative entropies in the extended reals, where $0\cdot(+\infty)=0$. $I(A;B|C)$, $H(A|B)$ and $D$ are the published definitions. Since all five statements are true, proving each of them proves the equivalence.
--
--   Differences from the source:
--   - encoding: "the following statements are equivalent, in the sense that one can prove the other statements as a consequence of one of them" → List.TFAE of the five statements, each a closed proposition quantified over all finite index types; reason: the Lean notion of equivalence of propositions; the quantification is the book's
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.9.2, p. 348

import Mathlib
import Definitions.Def_WildeQIT_QMemory_qRelEntropy
import Definitions.Def_WildeQIT_QMemory_qCondEntropy
import Definitions.Def_WildeQIT_AFW_qCondMutualInfo
import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_partialTrace

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 11.9.2, p. 348.
-/

namespace WildeQIT.Compression.Supplement

/-- **Theorem 11.9.2** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 348): "The following statements are equivalent, in the sense
that one can prove the other statements as a consequence of one of them:
1. The quantum relative entropy is monotone with respect to quantum channels:
   `D(ρ‖σ) ≥ D(N(ρ)‖N(σ))`, where `ρ, σ ∈ D(H)`, and `N : L(H) → L(H′)` is a quantum channel.
2. The quantum relative entropy is monotone with respect to partial trace:
   `D(ρ_AB‖σ_AB) ≥ D(ρ_B‖σ_B)`, where `ρ_AB, σ_AB ∈ D(H_A ⊗ H_B)`.
3. The quantum relative entropy is jointly convex: `∑_x p_X(x) D(ρ_x‖σ_x) ≥ D(ρ‖σ)`, where `p_X`
   is a probability distribution over a finite alphabet `X`, `ρ_x, σ_x ∈ D(H)` for all `x ∈ X`,
   `ρ ≡ ∑_x p_X(x) ρ_x`, and `σ ≡ ∑_x p_X(x) σ_x`.
4. The conditional quantum mutual information is non-negative: `I(A;B|C)_ρ ≥ 0`, where
   `ρ_ABC ∈ D(H_A ⊗ H_B ⊗ H_C)`.
5. The conditional quantum entropy is concave: `H(A|B)_ρ ≥ ∑_x p_X(x) H(A|B)_{ρ_x}`, where `p_X`
   is a probability distribution on a finite alphabet `X`, `ρ^x_AB ∈ D(H_A ⊗ H_B)` for all
   `x ∈ X`, and `ρ_AB ≡ ∑_x p_X(x) ρ^x_AB`."

Formalization Note: `List.TFAE` of five closed propositions, each universally quantified over all
finite index types (every finite-dimensional Hilbert space), all states, channels and finite
ensembles, as the book's statements are. `D` is the published `EReal`-valued
`WildeQIT.QMemory.qRelEntropy`; in statement 3 the weights multiply in `EReal`, where
`0 · (+∞) = 0` (a letter of probability zero contributes nothing). `I(A;B|C)` is the published
`WildeQIT.AFW.qCondMutualInfo` on `A × (B × C)`, `H(A|B)` the published
`WildeQIT.QMemory.qCondEntropy`, `ρ_B = Tr_A` the published `WildeQIT.partialTraceLeft`, and
distributions the published `WildeQIT.FinDist`. All five statements are true, so proving each of
them outright proves the equivalence. -/
theorem theorem_11_9_2 :
    List.TFAE
      [ ∀ (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
          (ρ σ : Matrix a a ℂ), IsDensityOperator ρ → IsDensityOperator σ →
          ∀ N : QChannel a b,
            WildeQIT.QMemory.qRelEntropy (N.apply ρ) (N.apply σ) ≤
              WildeQIT.QMemory.qRelEntropy ρ σ,
        ∀ (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
          (ρ σ : Matrix (a × b) (a × b) ℂ), IsDensityOperator ρ → IsDensityOperator σ →
            WildeQIT.QMemory.qRelEntropy (WildeQIT.partialTraceLeft ρ)
                (WildeQIT.partialTraceLeft σ) ≤ WildeQIT.QMemory.qRelEntropy ρ σ,
        ∀ (h X : Type) [Fintype h] [DecidableEq h] [Fintype X] (p : FinDist X)
          (ρ σ : X → Matrix h h ℂ), (∀ x, IsDensityOperator (ρ x)) →
            (∀ x, IsDensityOperator (σ x)) →
            WildeQIT.QMemory.qRelEntropy (∑ x, ((p.prob x : ℝ) : ℂ) • ρ x)
                (∑ x, ((p.prob x : ℝ) : ℂ) • σ x) ≤
              ∑ x, ((p.prob x : ℝ) : EReal) * WildeQIT.QMemory.qRelEntropy (ρ x) (σ x),
        ∀ (A B C : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
          [Fintype C] [DecidableEq C] (ρ : Matrix (A × (B × C)) (A × (B × C)) ℂ),
            IsDensityOperator ρ → 0 ≤ WildeQIT.AFW.qCondMutualInfo ρ,
        ∀ (A B X : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype X]
          (p : FinDist X) (ρ : X → Matrix (A × B) (A × B) ℂ), (∀ x, IsDensityOperator (ρ x)) →
            ∑ x, p.prob x * WildeQIT.QMemory.qCondEntropy (ρ x) ≤
              WildeQIT.QMemory.qCondEntropy (∑ x, ((p.prob x : ℝ) : ℂ) • ρ x) ] := by sorry

end WildeQIT.Compression.Supplement
