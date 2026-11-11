-- Prove2me | Theorems.Thm_SmallBiasPRF_theorem_7
-- name    : SmallBiasPRF.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:43.701617+00:00
-- url     : https://prove2.me/theorems/e01f1a41-ac1c-4fdc-9349-413cc9ef83ba
-- title:
--   Theorem 7 — the short-key expander-walk construction generates a $2^{-2n}$-biased space
-- statement:
--   Let $\Gamma$ be an undirected $d$-regular multigraph on $[m_1]$ whose second largest singular value is $\lambda\le1/192$. Let $H:\mathbb F_2^n\to\mathbb F_2^{m_1}$ be a linear code of minimum relative distance at least $7/16$, and let $R:\mathbb F_2^{m_2}\to\mathbb F_2^n$ be a linear perfect $k$-ERF with
--
--   $$m_2\ \ge\ 4096(n+m_1)+k-1 .$$
--
--   Then the short-key construction $\tilde F_{k_e,w,z}(a)=R(G_{w,z}(\mathrm{map}_{\tilde\pi_{k_e}}(H(a))))$, with key $(k_e,w,z)$ uniform on $K_{\exp}\times\{0,1,2\}^{m_2}\times\{0,1,2\}^{m_2}$, generates an $\varepsilon$-biased space with $\varepsilon\le 2^{-2n}$: for every nonempty $A\subseteq\{0,1\}^n$ and every family of nonempty masks $T_a\subseteq[n]$,
--
--   $$\Big|\mathop{\mathbb E}_{k_e,w,z}\Big[(-1)^{\sum_{a\in A}\sum_{j\in T_a}\tilde F_{k_e,w,z}(a)_j}\Big]\Big|\le 2^{-2n}.$$
--
--   This is the paper's main technical theorem: with linear-time encodable codes, explicit expanders and the transposition principle it yields keyed functions with $O(n)$-size circuits, $O(n)$-bit keys and exponentially small bias against all linear tests (Corollary 9).
--
--   **Formalization Note** $m_1,d,n\ge1$ are the paper's standing assumptions; the ERF property is Definition 1 (which includes $1\le k\le m_2$).
--
--   Differences from the source:
--   - generalization: Γ a finite undirected d-regular multigraph on [m₁] with labelled incidences → NB : Fin m₁ → Fin d → Fin m₁ with symmetric incidence counts #{e : NB x e = y} = #{e : NB y e = x} (IsUndirected); reason: the proof uses only the symmetry and regularity of the adjacency matrix; every undirected d-regular multigraph satisfies the condition, which in addition admits an odd number of loop incidences at a vertex
--   - encoding: second largest singular value λ ≤ 1/192, defined as ‖E_Γ − U‖_op = λ on L²(Ω) with the uniform probability measure → ‖adjMatrix NB − avgMatrix‖ ≤ 1/192 in the Euclidean operator norm of real matrices (IsSpectralExpander); reason: the paper's own definition; rescaling the inner product does not change operator norms
--   - encoding: H a linear code of minimum relative distance at least 7/16 → H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2) with (7/16)·m₁ ≤ wt(H v) for all v ≠ 0 (HasMinRelDist); reason: for a linear code the minimum distance is the minimum weight of a nonzero codeword; same instances
--   - encoding: 1-based indices; s_j defined recursively mod 3; t_j = ((s_j + z_j) mod 3) mod 2; keys in {0,1,2}^{m₂} → 0-based Fin indices; s_j = Σ_{i≤j} b_i w_i in ZMod 3 with bits lifted by value; t_j from the representative (s_j + z_j).val; keys Fin m₂ → ZMod 3; reason: Lean convention; the prefix sum is the unrolled recursion, and .val is the canonical representative in {0,1,2}; same function
--   - encoding: F̃ generates an ε-biased space with ε ≤ 2^{−2n} → GeneratesBiasedSpace (uniform key) F̃ (2^{−2n}); reason: being ε-biased is monotone in ε, so the two are equivalent
--   - encoding: k_e = (x₁, e₁, …, e_{m₂−1}) ∈ Ω × [d]^{m₂−1}, x_{j+1} = NB(x_j, e_j), key uniform → KeyExp = Fin m₁ × (Fin (m₂ − 1) → Fin d), walk 0 = x₁, walk (j+1) = NB (walk j) (e j); uniform key = PMF.uniformOfFintype / uavg over the finite key type; reason: 0-based indexing; m₂ ≥ 1 under the hypotheses, so the same walk and the same uniform law
--   - encoding: Pr[R(x) = y | x_{i_j} = x′_j for all j ∈ [c₁ − k]] = 2^{−c₂}, x′ ∈ F₂^{c₁−k} indexed through I = {i₁, …, i_{c₁−k}} → #{x : x agrees with x′ on I ∧ R x = y} · 2^{c₂} = #{x : x agrees with x′ on I}, x′ a full vector Fin c₁ → ZMod 2 read only on I (IsPerfectERF); reason: the conditioning event has 2^k > 0 elements, so the multiplied counting form is the conditional probability; a vector read on I carries exactly the same assignments; same instances
--   - encoding: E_{κ∼ν}[(−1)^{Σ_{a∈A} Σ_{j∈T_a} F_κ(a)_j}] with an integer exponent and masks {T_a}_{a∈A}, T_a ⊆ [n] → exponent summed in ZMod 2 and read through .val; masks a function T : F₂ⁿ → Finset (Fin n) constrained only on A; expectation Σ_κ ν(κ)·f(κ) (GeneratesBiasedSpace); reason: the sign depends only on the parity of the exponent and values of T off A are never read; same instances
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Theorem 7, p.16 (PDF 19)

import Mathlib
import Definitions.Def_SmallBiasPRF_IsPerfectERF
import Definitions.Def_SmallBiasPRF_GeneratesBiasedSpace
import Definitions.Def_SmallBiasPRF_HasMinRelDist
import Definitions.Def_SmallBiasPRF_Ftilde

namespace SmallBiasPRF

/-- **Theorem 7** (short-key construction is `2^{−2n}`-biased), p.16 (PDF p.19).
Dinur–Ishai, *Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with
Exponentially Small Bias*, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Theorem 7, p.16 (PDF p.19).

Let `Γ` be an undirected `d`-regular multigraph on `[m₁]` whose second largest singular value
is `λ ≤ 1/192`. For every linear code `H : 𝔽₂ⁿ → 𝔽₂^{m₁}` of minimum relative distance at least
`7/16` and every linear and perfect `k`-ERF `R : 𝔽₂^{m₂} → 𝔽₂ⁿ` with
`m₂ ≥ 4096(n + m₁) + k − 1`, the short-key construction `F̃`, with uniform key
`(k_e, w, z) ∈ K_exp × {0,1,2}^{m₂} × {0,1,2}^{m₂}`, generates an `ε`-biased space with
`ε ≤ 2^{−2n}`.

**Formalization Note.** `Γ` is its neighbour function `NB : Fin m₁ → Fin d → Fin m₁` with
symmetric incidence counts (`IsUndirected`); `λ ≤ 1/192` is `‖E_Γ − U‖_op ≤ 1/192`
(`IsSpectralExpander`). `m₁ ≥ 1`, `d ≥ 1` and `n ≥ 1` are the paper's standing assumptions
(`NeZero`); `m₂ ≥ 1` follows from the hypothesis on `m₂`. The ERF property is Definition 1
(`IsPerfectERF`, which includes `1 ≤ k ≤ m₂`). The key is uniform on `FullKey m₁ m₂ d`. -/
theorem theorem_7 (n m₁ m₂ k d : ℕ) [NeZero n] [NeZero m₁] [NeZero d]
    (NB : Fin m₁ → Fin d → Fin m₁) (hund : IsUndirected NB)
    (hspec : IsSpectralExpander NB (1 / 192))
    (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2)) (hH : HasMinRelDist H (7 / 16))
    (R : (Fin m₂ → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (hR : IsPerfectERF R k)
    (hm₂ : 4096 * (n + m₁) + k - 1 ≤ m₂) :
    GeneratesBiasedSpace (PMF.uniformOfFintype (FullKey m₁ m₂ d)) (Ftilde H R NB)
      ((2 : ℝ) ^ (-(2 * (n : ℤ)))) := by sorry

end SmallBiasPRF
