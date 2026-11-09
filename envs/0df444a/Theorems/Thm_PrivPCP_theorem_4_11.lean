-- Prove2me | Theorems.Thm_PrivPCP_theorem_4_11
-- name    : PrivPCP.theorem_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:44:44.907477+00:00
-- url     : https://prove2.me/theorems/005fa5a2-517d-4932-bd3b-57e830cee114
-- title:
--   Theorem 4.11: two-dimensional product expansion of subgroup Reed–Solomon codes
-- statement:
--   There is an absolute constant $c>0$ with the following property. Fix $\varepsilon\in(0,1)$ and $K\ge1$. There is a constant $\rho\in(0,1]$ with
--   $$\rho\ge c\,\frac{\varepsilon^6}{K^3}$$
--   such that: for every prime $q$, all multiplicative subgroups $S_1,S_2\le\mathbb F_q^\times$ of coprime orders $n_i=|S_i|$ with $K^{-1}\le n_1/n_2\le K$, and all integers $1\le k_i\le(1-\varepsilon)n_i$, the pair $(\mathrm{RS}(S_1,k_1),\mathrm{RS}(S_2,k_2))$ is $\rho$-product-expanding, and so is the pair after independently rescaling the coordinates of the two codes by nonzero field elements.
--
--   Equivalently, the property of Conjecture 4.2 holds at arity $r=2$ with $\eta=\varepsilon$, $\beta=K$. In contrast with Polishchuk–Spielman, which needs the sum of the two rates below one, each rate only has to be below $1-\varepsilon$. This is what makes the case $k=2$ of the main result unconditional.
--
--   **Formalization Note** The statement is $\mathrm{PunctRSPE}(2,\varepsilon,K,\rho)$, which contains the unscaled pair ($\Lambda_i=1$).
--
--   Differences from the source:
--   - reading: $\rho=\Omega(\varepsilon^6/K^3)\in(0,1]$ → there is an absolute $c>0$ with $c\varepsilon^6/K^3\le\rho\le1$; reason: the standard meaning of $\Omega(\cdot)$ with an absolute constant
--   - encoding: the unscaled and rescaled pairs, $K^{-1}\le n_1/n_2\le K$ → $\mathrm{PunctRSPE}(2,\varepsilon,K,\rho)$: diagonal rescalings $\Lambda_i$, $K^{-1}\le s_i/s_j\le K$ for $i,j\in\{1,2\}$; reason: $\Lambda_i=1$ gives the unscaled pair, and the two balance conditions are equivalent
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Theorem 4.11, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_PrivPCP_PunctRSPE

namespace PrivPCP

/-- **Theorem 4.11 (Two-dimensional product expansion of subgroup Reed–Solomon codes)** (Bafna, Vyas, *Private
PCPs from Product Expansion*, STOC 2027 submission manuscript (sha256 c2cac1e0…), Theorem 4.11, p.22). There is
an absolute constant `c > 0` such that for every `ε ∈ (0,1)` and `K ⩾ 1` there is `ρ ∈ (0,1]` with
`ρ ⩾ c ε⁶/K³` such that: for every prime `q`, all subgroups `S_1, S_2 ⩽ 𝔽_q^×` of coprime orders `n_i` with
`K^{−1} ⩽ n_1/n_2 ⩽ K`, all integers `1 ⩽ k_i ⩽ (1 − ε)n_i`, the pair `(RS(S_1, k_1), RS(S_2, k_2))` is
`ρ`-product-expanding, also after independently rescaling the coordinates of the two codes by nonzero field
elements.

**Formalization Note** "`ρ = Ω(ε⁶/K³)`" is read as the absolute `c` above. The rescaled conclusion (which
contains the unscaled one, `Λ = 1`) is exactly the arity-2 predicate `PunctRSPE 2 ε K ρ` of Conjecture 4.2. -/
theorem theorem_4_11 : ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ K : ℝ, 1 ≤ K →
    ∃ ρ : ℝ, c * ε ^ 6 / K ^ 3 ≤ ρ ∧ ρ ≤ 1 ∧ PunctRSPE 2 ε K ρ := by sorry

end PrivPCP
