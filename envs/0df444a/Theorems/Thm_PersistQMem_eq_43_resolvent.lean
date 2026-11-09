-- Prove2me | Theorems.Thm_PersistQMem_eq_43_resolvent
-- name    : PersistQMem.eq_43_resolvent
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:46:37.157613+00:00
-- url     : https://prove2.me/theorems/eb9c461d-49ec-4830-8bce-9ce0f3e4dece
-- title:
--   (43) — resolvent bounds $0\preceq f_\alpha(H)-H=H^2(\alpha I-H)^{-1}\preceq I/(\alpha-1)$, $\|f_\alpha(H)\|_{\mathrm{op}}\le\alpha/(\alpha-1)$
-- statement:
--   Let $\alpha>1$ and let $H$ be a Hermitian contraction ($-I\preceq H\preceq I$) of any finite dimension. Then $\alpha I-H$ is invertible, and the resolvent transformation $f_\alpha(H)=\alpha H(\alpha I-H)^{-1}$ of (42) satisfies
--   $$0\preceq f_\alpha(H)-H=H^2(\alpha I-H)^{-1}\preceq\frac{I}{\alpha-1},\qquad\|f_\alpha(H)\|_{\mathrm{op}}\le\frac\alpha{\alpha-1}.\tag{43}$$
--
--   These bounds control the penalty of regularizing the terminal test in §6.5.
--
--   Differences from the source:
--   - encoding: (αI − H)⁻¹ in (42)–(43) → Mathlib's total matrix inverse, with invertibility of αI − H stated as a conclusion; reason: Lean's inverse is defined for every matrix; the conclusion excludes the junk value
--   - encoding: Hermitian contraction −I ⪯ H ⪯ I → H Hermitian with 1 − H and 1 + H positive semidefinite; reason: Lean convention; same matrices
--   - encoding: ‖·‖_op → opNorm, Mathlib's l2 operator norm on matrices; reason: Lean convention; same norm
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), §6.4, (42)–(43), p.23 (PDF p.26)

import Mathlib
import Definitions.Def_PersistQMem_drift

open scoped Matrix ComplexOrder

namespace PersistQMem

/-- **(43), p.23: resolvent bounds** (Tao, Shen, *Structural Lower Bounds for Quantum Property
Estimation with Persistent Memory*, STOC 2027 submission, manuscript of 2026-11-03,
sha256 6d48ad24…, §6.4, (42)–(43), p.23). For `α > 1` and every Hermitian contraction `H`
(`−I ⪯ H ⪯ I`) of any finite dimension, `αI − H` is invertible and
`0 ⪯ f_α(H) − H = H²(αI − H)⁻¹ ⪯ I/(α − 1)` and `‖f_α(H)‖_op ≤ α/(α − 1)`,
with `f_α(H) = αH(αI − H)⁻¹` (42). -/
theorem eq_43_resolvent {n : Type} [Fintype n] [DecidableEq n] (α : ℝ) (hα : 1 < α)
    (H : Matrix n n ℂ) (hH : IsHermContraction H) :
    IsUnit ((α : ℂ) • (1 : Matrix n n ℂ) - H) ∧
    fAlpha α H - H = H * H * ((α : ℂ) • (1 : Matrix n n ℂ) - H)⁻¹ ∧
    (fAlpha α H - H).PosSemidef ∧
    ((((α - 1)⁻¹ : ℝ) : ℂ) • (1 : Matrix n n ℂ) - (fAlpha α H - H)).PosSemidef ∧
    opNorm (fAlpha α H) ≤ α / (α - 1) := by sorry

end PersistQMem
