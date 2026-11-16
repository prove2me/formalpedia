-- Prove2me | Theorems.Thm_SmallBiasPRF_Supplement_theorem_6
-- name    : SmallBiasPRF.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:06:25.024697+00:00
-- url     : https://prove2.me/theorems/d668a8dc-c947-4898-bddc-7abbcaf17285
-- title:
--   Theorem 6 — single-bit bias of the basic construction with uniform selector
-- statement:
--   Let $H:\mathbb F_2^n\to\mathbb F_2^{m_1}$ be a linear code. The basic construction's single-bit variant is
--   $$F^S_{\pi,w,z}(a)=G^S_{w,z}\big(\mathrm{map}_\pi(H(a))\big)=\sum_{j\in S}t_j \bmod 2,$$
--   where $(t_1,\dots,t_{m_2})=G_{w,z}(\mathrm{map}_\pi(H(a)))$, $\mathrm{map}_\pi(u)_j=u_{\pi(j)}$, and the key $(\pi,w,z)$ is uniform on $[m_1]^{m_2}\times\{0,1,2\}^{m_2}\times\{0,1,2\}^{m_2}$ (the uniform coordinate selector of §4.2).
--
--   Fix a nonempty set $A\subseteq\{0,1\}^n$ and subsets $\{S_a\}_{a\in A}$ of $[m_2]$ with
--   $$|S_a|\ \ge\ 4096(n+m_1)\qquad\text{for every }a\in A.$$
--   Then for every linear code $H$ of minimum relative distance at least $7/16$,
--   $$\Big|\mathop{\mathbb E}_{\pi,w,z}\Big[(-1)^{\sum_{a\in A}F^{S_a}_{\pi,w,z}(a)}\Big]\Big|\ \le\ \mathop{\mathbb E}_{\pi,w}\Big[\Big|\mathop{\mathbb E}_{z}\Big[(-1)^{\sum_{a\in A}F^{S_a}_{\pi,w,z}(a)}\Big]\Big|\Big]\ \le\ 2^{-2n}.\tag{2}$$
--
--   This is the single-bit theorem from which the paper derives Theorem 4 (via the reduction to single-bit masks, Lemma 10); it involves no compression map $R$.
--
--   **Formalization Note** $n,m_1\ge1$ are the paper's standing assumptions; $\pi$, $w$, $z$ are independent and uniform, expectations are uniform averages, and both inequalities of (2) are stated.
--
--   Differences from the source:
--   - encoding: H a linear code of minimum relative distance at least 7/16 → H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2) with (7/16)·m₁ ≤ wt(H v) for all v ≠ 0 (HasMinRelDist); reason: for a linear code the minimum distance is the minimum weight of a nonzero codeword; same instances
--   - encoding: 1-based indices; s_j defined recursively mod 3; t_j = ((s_j + z_j) mod 3) mod 2; keys in [m₁]^{m₂} × {0,1,2}^{m₂} × {0,1,2}^{m₂} → 0-based Fin indices; s_j = Σ_{i≤j} b_i w_i in ZMod 3 with bits lifted by value; t_j from the representative (s_j + z_j).val; keys Fin m₂ → Fin m₁ and Fin m₂ → ZMod 3 (published basicFS); reason: Lean convention; the prefix sum is the unrolled recursion and .val is the canonical representative in {0,1,2}; same function
--   - encoding: E over uniform (π, w, z), (π, w), z; exponent an integer sum; {S_a}_{a∈A} → uavg over the finite key types; exponent summed in ZMod 2 and read through paritySign; S a function F₂ⁿ → Finset (Fin m₂) constrained only on A; reason: uniform expectation is the average; the sign depends only on the parity; values of S off A are never read; same instances
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Theorem 6, display (2), p.15 (PDF 18)

import Mathlib
import Definitions.Def_SmallBiasPRF_GeneratesBiasedSpace
import Definitions.Def_SmallBiasPRF_HasMinRelDist
import Definitions.Def_SmallBiasPRF_basicF

namespace SmallBiasPRF.Supplement

open SmallBiasPRF

/-- **Theorem 6** (single-bit bias of the basic construction), display (2), p.15 (PDF p.18).
Dinur–Ishai, *Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with
Exponentially Small Bias*, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…),
Theorem 6, display (2), p.15 (PDF p.18).

Fix a nonempty `A ⊆ {0,1}ⁿ` and subsets `{S_a}_{a∈A}`, `S_a ⊆ [m₂]`, with `|S_a| ≥ 4096(n + m₁)`
for every `a ∈ A`. Then, for every linear code `H : 𝔽₂ⁿ → 𝔽₂^{m₁}` of minimum relative distance
at least `7/16`,
`|E_{π,w,z}[(−1)^{∑_{a∈A} F^{S_a}_{π,w,z}(a)}]| ≤ E_{π,w}[|E_z[(−1)^{∑_{a∈A} F^{S_a}_{π,w,z}(a)}]|] ≤ 2^{−2n}`.

**Formalization Note.** `π`, `w`, `z` are independent and uniform on `Fin m₂ → Fin m₁`,
`Fin m₂ → ZMod 3`, `Fin m₂ → ZMod 3` (§4.2: the basic construction's uniform selector);
expectations are uniform averages (`uavg`). `F^S` is the published `basicFS`; the exponent is
summed in `ZMod 2` and read through `paritySign`. The family `S` is a function on all of `𝔽₂ⁿ`,
constrained only on `A`. `n, m₁ ≥ 1` are the paper's standing assumptions. No `R` occurs. Both
inequalities of (2) are stated. -/
theorem theorem_6 (n m₁ m₂ : ℕ) [NeZero n] [NeZero m₁]
    (A : Finset (Fin n → ZMod 2)) (hA : A.Nonempty) (Sfam : (Fin n → ZMod 2) → Finset (Fin m₂))
    (hS : ∀ a ∈ A, 4096 * (n + m₁) ≤ (Sfam a).card)
    (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2)) (hH : HasMinRelDist H (7 / 16)) :
    |uavg fun κ : (Fin m₂ → Fin m₁) × (Fin m₂ → ZMod 3) × (Fin m₂ → ZMod 3) =>
        paritySign (∑ a ∈ A, basicFS H (Sfam a) κ.1 κ.2.1 κ.2.2 a)| ≤
        uavg (fun pw : (Fin m₂ → Fin m₁) × (Fin m₂ → ZMod 3) =>
          |uavg fun z : Fin m₂ → ZMod 3 => paritySign (∑ a ∈ A, basicFS H (Sfam a) pw.1 pw.2 z a)|) ∧
      uavg (fun pw : (Fin m₂ → Fin m₁) × (Fin m₂ → ZMod 3) =>
          |uavg fun z : Fin m₂ → ZMod 3 => paritySign (∑ a ∈ A, basicFS H (Sfam a) pw.1 pw.2 z a)|) ≤
        (2 : ℝ) ^ (-(2 * (n : ℤ))) := by sorry

end SmallBiasPRF.Supplement
