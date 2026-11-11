-- Prove2me | Theorems.Thm_PreservePast_eq_40
-- name    : PreservePast.eq_40
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:40:36.59409+00:00
-- url     : https://prove2.me/theorems/4bb6e70c-4d05-4fa6-9eef-f6dfc324874f
-- title:
--   (40) — energy bounds for one task: $C\succeq0$, $\operatorname{tr}C\le2$, $\|G\|_*\le\mathbb E[\|W_0X-Y\|\|X\|]\le\sqrt2$
-- statement:
--   Let $(X,Y)$ be an old task for the checkpoint $W_0\in\mathbb R^{m\times n}$, that is $\mathbb E\|X\|^2\le2$ and $\mathbb E\|W_0X-Y\|^2\le1$, with covariance $C=\mathbb E[XX^\top]$ and gradient $G=\mathbb E[(W_0X-Y)X^\top]$. Then
--   $$
--   C\succeq0,\qquad \operatorname{tr}C\le2,\qquad \|G\|_*\le\mathbb E\big[\|W_0X-Y\|\,\|X\|\big]\le\sqrt2,
--   $$
--   where $\|G\|_*$ is the nuclear norm (the sum of the singular values).
--
--   These bounds place the covariance in the nuclear ball of radius $2$ and the gradient in the nuclear ball of radius $\sqrt2$, which is what the finite codes of Lemma 4 and Theorem 9 quantize.
--
--   **Formalization Note** The expectation $\mathbb E[\|W_0X-Y\|\|X\|]$ is a lower Lebesgue integral; the statement asserts that it is at most $\sqrt2$ and that $\|G\|_*$ is at most its (finite) value.
--
--   Differences from the source:
--   - encoding: 𝔼[‖W₀X − Y‖‖X‖] as an expectation → lower Lebesgue integral, its real value used in the nuclear-norm comparison; reason: no junk value for a non-integrable integrand; the integral is finite by the second clause, so same instances
--   - encoding: C_i, G_i for task i of K → one task T; reason: the bounds are per task; same instances
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §C.1, p.17 (PDF p.19), (40)

import Mathlib
import Definitions.Def_PreservePast_Task
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm

open MeasureTheory Matrix

namespace PreservePast

/-- **(40): energy bounds for one task.** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §C.1, p.17 (PDF p.19): "The energy assumptions
give C_i ⪰ 0, tr C_i ≤ 2, ‖G_i‖_* ≤ 𝔼[‖W₀X − Y‖‖X‖] ≤ √2. (40)"

**Formalization Note.** `‖·‖_*` is the nuclear norm (sum of singular values). The expectation
`𝔼[‖W₀X − Y‖‖X‖]` is a lower Lebesgue integral; the statement asserts it is at most `√2` (hence
finite) and that the nuclear norm of `G` is at most its real value. -/
theorem eq_40 {m n : ℕ} (W₀ : Matrix (Fin m) (Fin n) ℝ) (T : Task W₀) :
    T.cov.PosSemidef ∧ T.cov.trace ≤ 2 ∧
      WainwrightHDS.NucNorm.nucNorm T.grad ≤
        (∫⁻ z, ENNReal.ofReal (Real.sqrt (∑ j, (W₀ *ᵥ z.1 - z.2) j ^ 2) *
          Real.sqrt (∑ i, z.1 i ^ 2)) ∂T.law).toReal ∧
      ∫⁻ z, ENNReal.ofReal (Real.sqrt (∑ j, (W₀ *ᵥ z.1 - z.2) j ^ 2) *
          Real.sqrt (∑ i, z.1 i ^ 2)) ∂T.law ≤ ENNReal.ofReal (Real.sqrt 2) := by sorry

end PreservePast
