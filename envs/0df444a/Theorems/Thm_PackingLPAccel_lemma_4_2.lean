-- Prove2me | Theorems.Thm_PackingLPAccel_lemma_4_2
-- name    : PackingLPAccel.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:07.613208+00:00
-- url     : https://prove2.me/theorems/4806bd3c-ea44-4eaf-a89c-90bfbf13fca7
-- title:
--   Lemma 4.2 — the signed reformulation $H$ of the residual problem
-- statement:
--   For an instance of Problem 1.3, every $z\in[0,\tilde u]$ gives a feasible update $\Delta=z^+-z^-$ with $-F(\Delta)\ge H(z)$. Every feasible $\Delta$ arises from some $z\in[0,\tilde u]$ with $H(z)=-F(\Delta)$. Consequently
--
--   $$\max_{0\le z\le\tilde u}H(z)=\mathrm{OPT}_{\mathrm{res}}=-\min_{\Delta\in\prod_jI_j}F(\Delta),$$
--
--   in the sense that a value is the maximum of $H$ exactly when its negative is the minimum of $F$.
--
--   This replaces each signed coordinate by two nonnegative ones, which is what the regression solver needs.
--
--   Differences from the source:
--   - encoding: max H = OPT_res → IsGreatest of H ↔ IsLeast of F; reason: avoids a real sSup on a set that the hypotheses do not make attained
--   - generalization: the two sides are compared at optima → the second clause holds for every feasible ∆; reason: it is the argument's own form, and yields equal suprema also without attainment
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), Lemma 4.2, p.13 (pdf 14)

import Mathlib
import Definitions.Def_PackingLPAccel_Residual

namespace PackingLPAccel

/-- **Lemma 4.2** (manuscript sha256 1dac7711…, p.13). The last clause is "`max H = OPT_res`": a value is the
maximum of `H` over `[0, ũ]` exactly when its negative is the minimum of `F` over `∏ I_j`. The middle clause gives
equality of the suprema also when no minimum is attained. -/
theorem lemma_4_2 {m n : ℕ} (R : ResidualInstance m n) (_ : R.IsValid) :
    (∀ z, R.InBoxT z → R.InBox (ResidualInstance.zToDelta z) ∧
      R.H z ≤ -R.F (ResidualInstance.zToDelta z)) ∧
    (∀ Δ, R.InBox Δ → ∃ z, R.InBoxT z ∧ ResidualInstance.zToDelta z = Δ ∧ R.H z = -R.F Δ) ∧
    ∀ v : ℝ, IsGreatest (R.H '' {z | R.InBoxT z}) v ↔ IsLeast (R.F '' {Δ | R.InBox Δ}) (-v) := by sorry

end PackingLPAccel
