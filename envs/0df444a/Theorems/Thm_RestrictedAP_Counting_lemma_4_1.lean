-- Prove2me | Theorems.Thm_RestrictedAP_Counting_lemma_4_1
-- name    : RestrictedAP.Counting.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:20:58.91231+00:00
-- url     : https://prove2.me/theorems/7d27601d-7337-4004-b5cd-a62d3098e255
-- title:
--   Lemma 4.1 — arithmetic regularity lemma for the operators $T_{\mathcal P,1-\varepsilon}$
-- statement:
--   For every $m$ there is $M=M(m)$ and, for every $\alpha>0$, a threshold decay function $w_0:(0,1)\times\mathbb N\to(0,1)$ such that for every two-argument decay function $w\le w_0$ ("sufficiently rapid"), every finite alphabet $\Sigma$ with $|\Sigma|\le m$, every distribution $\nu$ on $\Sigma$ with every atom of probability at least $\alpha$, and every $\xi>0$, there is $k\in\mathbb N$ such that, with $\varepsilon_0=1/2$ and $\varepsilon_{i+1}=w(\varepsilon_i,i)$: for every $1$-bounded $f:\Sigma^n\to\mathbb C$ and every $i_0\in\mathbb N$ there are $i_0\le i\le k+i_0$ and collections $\mathcal P,\mathcal P'$ of cyclic (normalized) product functions with
--
--   1. $|\mathcal P|\le1/\varepsilon_i$, $\mathcal P$ is $M$-discrete, and $\|f-T_{\mathcal P,1-\varepsilon'}f\|_\nu\le\xi$ for all $\varepsilon'\in[\varepsilon_{i+2},\varepsilon_{i+1})$;
--   2. $|\mathcal P'|\le1/\varepsilon_{i+4}$, $\mathcal P'$ is $M$-discrete, and $\|f-T_{\mathcal P',1-\varepsilon_{i+5}}f\|_\nu\le\varepsilon_{i+3}$;
--   3. $\|T_{\mathcal P',1-\varepsilon_{i+5}}f-T_{\mathcal P,1-\varepsilon'}f\|_2\le\xi$ for all $\varepsilon'\in[\varepsilon_{i+2},\varepsilon_{i+1})$.
--
--   Here $T_{\mathcal P,1-\varepsilon}=T_{\nu,\mathcal P,1-\varepsilon}$, $\|\cdot\|_\nu=\|\cdot\|_{\nu,\alpha}$ and $\|\cdot\|_2$ is the norm of $L^2(\nu^{\otimes n})$. The point is that the fine approximation $T_{\mathcal P'}f$ has an error $\varepsilon_{i+3}$ that is arbitrarily small compared with the size of the coarse collection $\mathcal P$, while staying $\xi$-close to it in $L^2$.
--
--   Differences from the source:
--   - reading: w a sufficiently rapid decay function → ∃ a decay function w₀ (depending on m, α) such that the conclusion holds for every decay function w with w ≤ w₀ on (0,1) × ℕ; reason: the usual meaning of 'sufficiently rapid'; w₀ is itself a decay function, so the class of admissible w is nonempty
--   - reading: O_m(1)-discrete → ∃ M = M(m), quantified before α, Σ, ν, w, ξ, f, and both collections are M-discrete; reason: §2 notation
--   - reading: 'Then for all ξ > 0, there exists k' → k is chosen after Σ, ν, w and ξ, before n, f and i₀; reason: the printed order
--   - reading: product functions (the theorem's sentence) → product functions normalized at a distinguished σ⋆: factors of modulus 1 with P_i(σ⋆) = 1 (`IsProductFunction σs`); reason: §2.1 (p. 7): 'Unless specified otherwise, throughout this paper we will consider normalized product functions'
--   - reading: ∥·∥_ν, M_ν with 'pairwise connected' (not defined in the paper) → `nuNorm ν α` with the α of the atom bound (Definition 2.19); pairwise connected = for each pair of coordinates the bipartite graph of pairs occurring in an atom of μ is connected on its non-isolated vertices; reason: Definition 2.19 'when α is clear from context we write ∥f∥_ν'; the [BKM24b] notion
--   - encoding: decay function w : (0,1) × ℕ → (0,1), monotonically increasing with w(ε) ≤ ε → w : ℝ → ℕ → ℝ with these properties required on (0,1) (`IsDecay2`); reason: values outside (0,1) are never used
--   - encoding: ord(P) ∈ ℕ ∪ {∞} → `orderOf P` in the monoid of functions (0 encodes ∞); M-discrete = 0 < orderOf P ≤ M; reason: Mathlib's order of an element is the least k ≥ 1 with P^k = 1, as Definition 2.3
--   - encoding: a collection 𝒫 of product functions and |𝒫| → a `Finset` of functions `(Fin n → Σ) → ℂ` and its card; reason: a collection is a set of functions
--   - encoding: distributions over finite alphabets, ν^{⊗n}, Pr and E → nonnegative weight functions summing to 1 (`IsDist`), product weights (`tensorPow`), finite sums; reason: finite probability spaces; same instances
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), p. 23, Lemma 4.1

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_ProductFunctions
import Definitions.Def_RestrictedAP_Counting_NoiseOperators
import Definitions.Def_RestrictedAP_Counting_Seminorms

namespace RestrictedAP.Counting

/-- **Lemma 4.1** (p. 23), the basic arithmetic regularity lemma. For every `m` there is
`M = O_m(1)`, and for every `α > 0` a threshold decay function `w₀` ("sufficiently rapid"), such
that for every decay function `w : (0,1) × ℕ → (0,1)` with `w ≤ w₀`, every finite alphabet `Σ`
with `|Σ| ≤ m`, every distribution `ν` on `Σ` with all atoms of probability at least `α`, and
every `ξ > 0`, there is `k ∈ ℕ` such that, with `ε₀ = 1/2`, `ε_{i+1} = w(ε_i, i)`: for every
`1`-bounded `f : Σ^n → ℂ` and every `i₀ ∈ ℕ` there are `i₀ ≤ i ≤ k + i₀` and collections `𝒫, 𝒫'`
of cyclic (normalized) product functions with
1. `|𝒫| ≤ 1/ε_i`, `𝒫` is `M`-discrete, and `‖f − T_{𝒫,1−ε'} f‖_ν ≤ ξ` for all
   `ε' ∈ [ε_{i+2}, ε_{i+1})`;
2. `|𝒫'| ≤ 1/ε_{i+4}`, `𝒫'` is `M`-discrete, and `‖f − T_{𝒫',1−ε_{i+5}} f‖_ν ≤ ε_{i+3}`;
3. `‖T_{𝒫',1−ε_{i+5}} f − T_{𝒫,1−ε'} f‖₂ ≤ ξ` for all `ε' ∈ [ε_{i+2}, ε_{i+1})`.
Here `‖·‖_ν = ‖·‖_{ν,α}` and `‖·‖₂` is the norm of `L²(ν^{⊗n})`. -/
theorem lemma_4_1 (m : ℕ) :
    ∃ M : ℕ, ∀ α : ℝ, 0 < α →
    ∃ w₀ : ℝ → ℕ → ℝ, IsDecay2 w₀ ∧
    ∀ w : ℝ → ℕ → ℝ, IsDecay2 w → (∀ ε i, 0 < ε → ε < 1 → w ε i ≤ w₀ ε i) →
    ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig] (σs : Sig) (ν : Sig → ℝ),
      Fintype.card Sig ≤ m → IsDist ν → AtomsAtLeast ν α →
    ∀ ξ : ℝ, 0 < ξ → ∃ k : ℕ,
    ∀ (n : ℕ) (f : (Fin n → Sig) → ℂ), (∀ x, ‖f x‖ ≤ 1) → ∀ i₀ : ℕ,
    ∃ i : ℕ, i₀ ≤ i ∧ i ≤ k + i₀ ∧
    ∃ PP PP' : Finset ((Fin n → Sig) → ℂ),
      (∀ P ∈ PP, IsProductFunction σs P ∧ IsCyclic P ∧ IsDiscrete M P) ∧
      (∀ P ∈ PP', IsProductFunction σs P ∧ IsCyclic P ∧ IsDiscrete M P) ∧
      -- item 1
      (PP.card : ℝ) ≤ 1 / decaySeq w i ∧
      (∀ ε' : ℝ, decaySeq w (i + 2) ≤ ε' → ε' < decaySeq w (i + 1) →
        nuNorm ν α (f - condNoise ν PP ε' f) ≤ ξ) ∧
      -- item 2
      (PP'.card : ℝ) ≤ 1 / decaySeq w (i + 4) ∧
      nuNorm ν α (f - condNoise ν PP' (decaySeq w (i + 5)) f) ≤ decaySeq w (i + 3) ∧
      -- item 3
      (∀ ε' : ℝ, decaySeq w (i + 2) ≤ ε' → ε' < decaySeq w (i + 1) →
        l2Norm (tensorPow ν n)
          (condNoise ν PP' (decaySeq w (i + 5)) f - condNoise ν PP ε' f) ≤ ξ) := by sorry

end RestrictedAP.Counting
