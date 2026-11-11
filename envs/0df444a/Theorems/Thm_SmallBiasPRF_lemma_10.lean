-- Prove2me | Theorems.Thm_SmallBiasPRF_lemma_10
-- name    : SmallBiasPRF.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:11:40.511687+00:00
-- url     : https://prove2.me/theorems/d80d7295-9251-4a3f-b818-2494171792c6
-- title:
--   Lemma 10 — reduction to single-bit masks for an arbitrary selector law
-- statement:
--   Consider the generalized construction $F$ in which the selector $\pi\in[m_1]^{m_2}$ is drawn from an arbitrary distribution $\nu$, independently of the uniform key $(w,z)$. Suppose there is $\varepsilon\ge0$ such that for every nonempty $A\subseteq\{0,1\}^n$ and every family $\{S_a\}_{a\in A}$ of subsets of $[m_2]$ with $|S_a|\ge 4096(n+m_1)$ for every $a\in A$,
--
--   $$\Big|\mathop{\mathbb E}_{\pi\sim\nu,w,z}\Big[(-1)^{\sum_{a\in A}F^{S_a}_{\pi,w,z}(a)}\Big]\Big|\le\varepsilon .$$
--
--   Suppose additionally that $R:\mathbb F_2^{m_2}\to\mathbb F_2^n$ is a linear perfect $k$-ERF with $m_2\ge 4096(n+m_1)+k-1$. Then the generalized construction generates an $\varepsilon$-biased space.
--
--   Together with Theorem 8 this yields the goal, Theorem 7: the walk selector of the short-key construction is one such law $\nu$.
--
--   **Formalization Note** Both the hypothesis and the conclusion use the key law $\nu\otimes\mathrm{Unif}(w,z)$. $H$ is an arbitrary linear map, as in the paper. $n,m_1\ge1$ are the paper's standing assumptions.
--
--   Differences from the source:
--   - encoding: 1-based indices; s_j defined recursively mod 3; t_j = ((s_j + z_j) mod 3) mod 2; keys in {0,1,2}^{m₂} → 0-based Fin indices; s_j = Σ_{i≤j} b_i w_i in ZMod 3 with bits lifted by value; t_j from the representative (s_j + z_j).val; keys Fin m₂ → ZMod 3; reason: Lean convention; the prefix sum is the unrolled recursion, and .val is the canonical representative in {0,1,2}; same function
--   - encoding: π ∈ [m₁]^{m₂} sampled from an arbitrary distribution ν independently of the uniform (w, z) → ν : PMF (Fin m₂ → Fin m₁); the joint law is ν bound with the uniform law on (w, z) (selKeyLaw ν), or pmfExp ν of uniform averages over w and z; reason: this is the product law the page describes; same distribution
--   - encoding: Pr[R(x) = y | x_{i_j} = x′_j for all j ∈ [c₁ − k]] = 2^{−c₂}, x′ ∈ F₂^{c₁−k} indexed through I = {i₁, …, i_{c₁−k}} → #{x : x agrees with x′ on I ∧ R x = y} · 2^{c₂} = #{x : x agrees with x′ on I}, x′ a full vector Fin c₁ → ZMod 2 read only on I (IsPerfectERF); reason: the conditioning event has 2^k > 0 elements, so the multiplied counting form is the conditional probability; a vector read on I carries exactly the same assignments; same instances
--   - encoding: E_{κ∼ν}[(−1)^{Σ_{a∈A} Σ_{j∈T_a} F_κ(a)_j}] with an integer exponent and masks {T_a}_{a∈A}, T_a ⊆ [n] → exponent summed in ZMod 2 and read through .val; masks a function T : F₂ⁿ → Finset (Fin n) constrained only on A; expectation Σ_κ ν(κ)·f(κ) (GeneratesBiasedSpace); reason: the sign depends only on the parity of the exponent and values of T off A are never read; same instances
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 10, p.17 (PDF 20)

import Mathlib
import Definitions.Def_SmallBiasPRF_IsPerfectERF
import Definitions.Def_SmallBiasPRF_GeneratesBiasedSpace
import Definitions.Def_SmallBiasPRF_basicF

namespace SmallBiasPRF

/-- **Lemma 10** (reduction to single-bit masks), p.17 (PDF p.20).
Dinur–Ishai, *Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with
Exponentially Small Bias*, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 10, p.17 (PDF p.20).

Consider the generalized construction `F` in which `π ∈ [m₁]^{m₂}` is sampled from an arbitrary
distribution `ν` independently of `(w, z)`. Suppose there is `ε ≥ 0` such that for every
nonempty `A ⊆ {0,1}ⁿ` and every family `{S_a}_{a∈A}`, `S_a ⊆ [m₂]`, with
`|S_a| ≥ 4096(n + m₁)` for every `a ∈ A`,
`|E_{π∼ν,w,z}[(−1)^{∑_{a∈A} F^{S_a}_{π,w,z}(a)}]| ≤ ε`.
Suppose additionally that `R : 𝔽₂^{m₂} → 𝔽₂ⁿ` is a linear and perfect `k`-ERF with
`m₂ ≥ 4096(n + m₁) + k − 1`. Then the generalized construction generates an `ε`-biased space.

**Formalization Note.** The key law is `selKeyLaw ν` (`π ∼ ν` independent of uniform `(w, z)`),
used both in the hypothesis and in the conclusion. `H` is any linear map (no distance hypothesis,
as in the paper). `n, m₁ ≥ 1` are the paper's standing assumptions. -/
theorem lemma_10 (n m₁ m₂ k : ℕ) [NeZero n] [NeZero m₁]
    (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2))
    (R : (Fin m₂ → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (ν : PMF (Fin m₂ → Fin m₁)) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hsingle : ∀ A : Finset (Fin n → ZMod 2), A.Nonempty →
      ∀ Sfam : (Fin n → ZMod 2) → Finset (Fin m₂), (∀ a ∈ A, 4096 * (n + m₁) ≤ (Sfam a).card) →
        |pmfExp (selKeyLaw ν)
            (fun κ => paritySign (∑ a ∈ A, basicFS H (Sfam a) κ.1 κ.2.1 κ.2.2 a))| ≤ ε)
    (hR : IsPerfectERF R k) (hm₂ : 4096 * (n + m₁) + k - 1 ≤ m₂) :
    GeneratesBiasedSpace (selKeyLaw ν) (fun κ a => basicF H R κ.1 κ.2.1 κ.2.2 a) ε := by sorry

end SmallBiasPRF
