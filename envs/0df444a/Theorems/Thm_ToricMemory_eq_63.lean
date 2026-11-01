-- Prove2me | Theorems.Thm_ToricMemory_eq_63
-- name    : ToricMemory.eq_63
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:21:35.925047+00:00
-- url     : https://prove2.me/theorems/98b6229f-8966-4f16-9800-93e5b911dd1a
-- title:
--   Eq. (63) — $4\mu_3^2<87.8$, so (63) implies (60)
-- statement:
--   The connective constant $\mu_3$ of the cubic lattice satisfies
--   $$
--   4\mu_3^2<87.8 .
--   $$
--   Consequently $\tilde p,\tilde q<(87.8)^{-1}$ implies the threshold condition (60), $\tilde p,\tilde q<(4\mu_3^2)^{-1}$, which is how the paper states its numerical threshold (63) from $\mu_3\approx4.684$.
--
--   Differences from the source:
--   - reading: "Numerically, the accuracy threshold is surely attained provided that p̃, q̃ < (87.8)^{−1} = .0113" (63), derived from μ₃ ≈ 4.684 → 4 * mu3 ^ 2 < 87.8 for the exact connective constant; reason: (63) is a sufficient condition exactly when (87.8)^{−1} ≤ (4μ₃²)^{−1}; the strict form is what the paper's numerics (4 · 4.684² ≈ 87.76) assert
--   - reading: μ₃ ≈ 4.684 (eq. (58)) → mu3 := inf_{n ≥ 1} c_n^{1/n}, the exact connective constant of ℤ³; reason: the decimal is the numerical value of the cubic lattice's connective constant, which is what the bound (58) is about
-- source:
--   Dennis, Kitaev, Landahl & Preskill, Topological quantum memory, arXiv:quant-ph/0110143v1, Sec. V C, eq. (63), p. 20

import Mathlib
import Definitions.Def_ToricMemory_CubicSAW

namespace ToricMemory

/-- **Eq. (63) implies eq. (60)**, arXiv:quant-ph/0110143v1, Sec. V C, p. 20 (PDF p. 20):
"Numerically, the accuracy threshold is surely attained provided that
`p̃, q̃ < (87.8)^{−1} = .0113`". The paper obtains (63) from (60) with `μ₃ ≈ 4.684`; the
statement that makes this step valid is `4μ₃² < 87.8` for the exact connective constant `μ₃`
of the cubic lattice. -/
theorem eq_63 : 4 * mu3 ^ 2 < 87.8 := by sorry

end ToricMemory
