-- Prove2me | Theorems.Thm_SmallBiasPRF_Supplement_theorem_4
-- name    : SmallBiasPRF.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:06:59.523196+00:00
-- url     : https://prove2.me/theorems/e9fb3b51-81f6-4a0c-9189-cf3a6da76c46
-- title:
--   Theorem 4 — the basic construction with uniform selector generates a $2^{-2n}$-biased space
-- statement:
--   Let $H:\mathbb F_2^n\to\mathbb F_2^{m_1}$ be a linear code of minimum relative distance at least $7/16$, and let $R:\mathbb F_2^{m_2}\to\mathbb F_2^n$ be a linear perfect $k$-ERF (Definition 1) with
--   $$m_2\ \ge\ 4096(n+m_1)+k-1 .$$
--   Then the basic construction
--   $$F_{\pi,w,z}(a)=R\big(G_{w,z}(\mathrm{map}_\pi(H(a)))\big),$$
--   with key $(\pi,w,z)$ uniform on $[m_1]^{m_2}\times\{0,1,2\}^{m_2}\times\{0,1,2\}^{m_2}$, generates an $\varepsilon$-biased space with $\varepsilon\le2^{-2n}$: for every nonempty $A\subseteq\{0,1\}^n$ and every family of nonempty masks $T_a\subseteq[n]$,
--   $$\Big|\mathop{\mathbb E}_{\pi,w,z}\Big[(-1)^{\sum_{a\in A}\sum_{j\in T_a}F_{\pi,w,z}(a)_j}\Big]\Big|\le 2^{-2n}.$$
--
--   With linear-time encodable codes it yields keyed functions with $O(n)$-size circuits, $O(n\log n)$-bit keys and exponentially small bias against all linear tests (Corollary 5); the expander-walk construction of Theorem 7 shortens the key to $O(n)$.
--
--   **Formalization Note** $n,m_1\ge1$ are the paper's standing assumptions; the ERF property is Definition 1 (which includes $1\le k\le m_2$); the selector $\pi$ is uniform on all of $[m_1]^{m_2}$.
--
--   Differences from the source:
--   - encoding: H a linear code of minimum relative distance at least 7/16 → H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2) with (7/16)·m₁ ≤ wt(H v) for all v ≠ 0 (HasMinRelDist); reason: for a linear code the minimum distance is the minimum weight of a nonzero codeword; same instances
--   - encoding: 1-based indices; s_j defined recursively mod 3; t_j = ((s_j + z_j) mod 3) mod 2; keys in [m₁]^{m₂} × {0,1,2}^{m₂} × {0,1,2}^{m₂}, uniform → 0-based Fin indices; s_j = Σ_{i≤j} b_i w_i in ZMod 3 with bits lifted by value; t_j from the representative (s_j + z_j).val; key PMF.uniformOfFintype on (Fin m₂ → Fin m₁) × (Fin m₂ → ZMod 3) × (Fin m₂ → ZMod 3) (published basicF); reason: Lean convention; the prefix sum is the unrolled recursion and .val is the canonical representative in {0,1,2}; same function and same uniform law
--   - encoding: F generates an ε-biased space with ε ≤ 2^{−2n} → GeneratesBiasedSpace (uniform key) F (2^{−2n}); reason: being ε-biased is monotone in ε, so the two are equivalent
--   - encoding: Pr[R(x) = y | x_{i_j} = x′_j for all j ∈ [c₁ − k]] = 2^{−c₂}, x′ ∈ F₂^{c₁−k} indexed through I → #{x : x agrees with x′ on I ∧ R x = y} · 2^{c₂} = #{x : x agrees with x′ on I}, x′ a full vector read only on I (IsPerfectERF); reason: the conditioning event has 2^k > 0 elements, so the multiplied counting form is the conditional probability; same instances
--   - encoding: E_{κ}[(−1)^{Σ_{a∈A} Σ_{j∈T_a} F_κ(a)_j}] with an integer exponent and masks {T_a}_{a∈A} → exponent summed in ZMod 2 and read through .val; masks a function T : F₂ⁿ → Finset (Fin n) constrained only on A (GeneratesBiasedSpace); reason: the sign depends only on the parity of the exponent and values of T off A are never read; same instances
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Theorem 4, p.14 (PDF 17)

import Mathlib
import Definitions.Def_SmallBiasPRF_IsPerfectERF
import Definitions.Def_SmallBiasPRF_GeneratesBiasedSpace
import Definitions.Def_SmallBiasPRF_HasMinRelDist
import Definitions.Def_SmallBiasPRF_basicF

namespace SmallBiasPRF.Supplement

open SmallBiasPRF

/-- **Theorem 4** (the basic construction with uniform selector is `2^{−2n}`-biased), p.14
(PDF p.17).
Dinur–Ishai, *Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with
Exponentially Small Bias*, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…),
Theorem 4, p.14 (PDF p.17).

For every linear code `H : 𝔽₂ⁿ → 𝔽₂^{m₁}` of minimum relative distance at least `7/16` and every
linear and perfect `k`-ERF `R : 𝔽₂^{m₂} → 𝔽₂ⁿ` with `m₂ ≥ 4096(n + m₁) + k − 1`, the basic
construction `F_{π,w,z}(a) = R(G_{w,z}(map_π(H(a))))`, with key `(π, w, z)` uniform on
`[m₁]^{m₂} × {0,1,2}^{m₂} × {0,1,2}^{m₂}` (§4.2), generates an `ε`-biased space with
`ε ≤ 2^{−2n}`.

**Formalization Note.** `n, m₁ ≥ 1` are the paper's standing assumptions (§4.1, `NeZero`);
`m₂ ≥ 1` follows from the hypothesis on `m₂`. The construction is the published `basicF`, the
bias notion the published `GeneratesBiasedSpace` (Definition 2), the code hypothesis
`HasMinRelDist` and the ERF property Definition 1 (`IsPerfectERF`, which includes `1 ≤ k ≤ m₂`).
The selector `π` is uniform on all of `Fin m₂ → Fin m₁` (independent coordinates); there is no
graph. -/
theorem theorem_4 (n m₁ m₂ k : ℕ) [NeZero n] [NeZero m₁]
    (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2)) (hH : HasMinRelDist H (7 / 16))
    (R : (Fin m₂ → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (hR : IsPerfectERF R k)
    (hm₂ : 4096 * (n + m₁) + k - 1 ≤ m₂) :
    GeneratesBiasedSpace
      (PMF.uniformOfFintype ((Fin m₂ → Fin m₁) × (Fin m₂ → ZMod 3) × (Fin m₂ → ZMod 3)))
      (fun κ : (Fin m₂ → Fin m₁) × (Fin m₂ → ZMod 3) × (Fin m₂ → ZMod 3) =>
        basicF H R κ.1 κ.2.1 κ.2.2)
      ((2 : ℝ) ^ (-(2 * (n : ℤ)))) := by sorry

end SmallBiasPRF.Supplement
