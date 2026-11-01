-- Prove2me | Theorems.Thm_ToricMemory_eq_58
-- name    : ToricMemory.eq_58
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:21:45.758905+00:00
-- url     : https://prove2.me/theorems/cc202b6f-db43-4eb8-a0ad-a424f04d58d6
-- title:
--   Eq. (58) — $n^{(3)}_{\rm SAP}(\ell)\le P_3(\ell)\,\mu_3^{\ell}$
-- statement:
--   There are a constant $C$ and an integer $k\ge0$ such that for every $\ell\ge0$ the number of rooted $\ell$-step self-avoiding polygons in $\mathbb Z^3$ satisfies
--   $$
--   n^{(3)}_{\rm SAP}(\ell)\;\le\;C(\ell+1)^k\mu_3^{\ell},
--   $$
--   where $\mu_3$ is the connective constant of the cubic lattice. The paper quotes this bound from the literature with a polynomial $P_3(\ell)$.
--
--   It is the counting input of the three-dimensional threshold.
--
--   Differences from the source:
--   - reading: μ₃ ≈ 4.684 (eq. (58)) → mu3 := inf_{n ≥ 1} c_n^{1/n}, the exact connective constant of ℤ³; reason: the decimal is the numerical value of the cubic lattice's connective constant, which is what the bound (58) is about
--   - encoding: P₃(ℓ) a polynomial → C(ℓ + 1)^k with C, k quantified before ℓ; reason: every polynomial is bounded by such an expression on ℓ ≥ 0, and each such expression is a polynomial
-- source:
--   Dennis, Kitaev, Landahl & Preskill, Topological quantum memory, arXiv:quant-ph/0110143v1, Sec. V C, eq. (58), p. 20

import Mathlib
import Definitions.Def_ToricMemory_CubicSAW

namespace ToricMemory

/-- **Eq. (58)**, arXiv:quant-ph/0110143v1, Sec. V C, p. 20 (PDF p. 20), citing [31, 32]:
`n_SAP^{(3)}(ℓ) ≤ P₃(ℓ)(μ₃)^ℓ` with `P₃` a polynomial and `μ₃ ≈ 4.684` the connective constant
of the cubic lattice. There are `C` and `k` such that the number of rooted `ℓ`-step
self-avoiding polygons in `ℤ³` is at most `C (ℓ + 1)^k μ₃^ℓ` for every `ℓ`.

**Formalization Note** The polynomial `P₃` is encoded as `C (ℓ + 1)^k`, which bounds every
polynomial on `ℓ ≥ 0`; `μ₃` is the exact connective constant `mu3`. -/
theorem eq_58 : ∃ C : ℝ, ∃ k : ℕ, ∀ ℓ : ℕ,
    (sapZ3 ℓ : ℝ) ≤ C * ((ℓ : ℝ) + 1) ^ k * mu3 ^ ℓ := by sorry

end ToricMemory
