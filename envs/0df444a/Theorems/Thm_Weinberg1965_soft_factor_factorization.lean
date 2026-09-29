-- Prove2me | Theorems.Thm_Weinberg1965_soft_factor_factorization
-- name    : Weinberg1965.soft_factor_factorization
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:52:56.041986+00:00
-- url     : https://prove2.me/theorems/25680911-62c2-4e9b-889c-316106ffe5ee
-- title:
--   Sec. II.2 — factorization of multiple soft-emission pole factors
-- statement:
--   Let $N\ge0$ and let $z_1,\dots,z_N$ be complex numbers such that every nonempty partial sum is nonzero: $\sum_{i\in S}z_i\ne0$ for every nonempty $S\subseteq\{1,\dots,N\}$. Then
--   $$\sum_{\sigma\in S_N}\ \prod_{k=1}^{N}\frac{1}{z_{\sigma(1)}+z_{\sigma(2)}+\cdots+z_{\sigma(k)}}=\prod_{i=1}^{N}\frac{1}{z_i}.$$
--
--   With $z_r=p\cdot q_r$ this is the statement of Sec. II.2: when $N$ soft photons (or gravitons) are attached to one external line, the charged-particle propagators give a multiple pole factor $[p\cdot q_r]^{-1}[p\cdot(q_r+q_s)]^{-1}\cdots$, and after summing over the $N!$ orderings the result is the product $[p\cdot q_1]^{-1}\cdots[p\cdot q_N]^{-1}$ of single-emission factors (the paper displays the case $N=2$ and states the general case follows by induction). This factorization is what makes the soft factors exponentiate in (2.11) and (2.19).
--
--   **Formalization Note** The identity is stated as an exact algebraic identity for complex numbers with nonvanishing partial sums; the paper's $-i\eta\epsilon$ prescriptions are suppressed (they only fix the treatment of the poles and are taken to zero). Indices run over `Fin N`, and the $k$-th partial sum is $\sum_{j\le k}z_{\sigma(j)}$.
-- source:
--   S. Weinberg, Infrared Photons and Gravitons, Phys. Rev. 140, B516 (1965), https://doi.org/10.1103/PhysRev.140.B516, pp. B517–B518, Sec. II.2 (display following Eq. (2.7))

import Definitions.Def_Weinberg1965_Defs

namespace Weinberg1965

theorem soft_factor_factorization (N : ℕ) (z : Fin N → ℂ)
    (hz : ∀ s : Finset (Fin N), s.Nonempty → ∑ i ∈ s, z i ≠ 0) :
    ∑ σ : Equiv.Perm (Fin N),
        ∏ k : Fin N, (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ≤ k), z (σ j))⁻¹
      = ∏ i : Fin N, (z i)⁻¹ := by
  sorry

end Weinberg1965
