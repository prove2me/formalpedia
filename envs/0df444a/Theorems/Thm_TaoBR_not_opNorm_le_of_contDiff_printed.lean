-- Prove2me | Theorems.Thm_TaoBR_not_opNorm_le_of_contDiff_printed
-- name    : TaoBR.not_opNorm_le_of_contDiff_printed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:06:04.385088+00:00
-- url     : https://prove2.me/theorems/71e24ced-c48a-42fb-900d-92107cfb54dd
-- title:
--   Tao 1999, Lemma 2.1 as printed, without derivative bounds uniform in y, is false
-- statement:
--   Lemma 2.1 fails when $b$ is only required to be smooth in $(x, \tau)$ for each $y$, with no bound on its derivatives uniform in $y$. Precisely: it is not the case that, for all $n$, $1 \le p, q \le \infty$, every family of measurable kernels $K_R$ on $\mathbf R^n \times \mathbf R^n$ bounded by $M$ and supported in one compact set $S$, and every bounded $b(x, y, \tau)$, measurable in $(x, y)$ and $C^\infty$ in $(x, \tau)$ on an open set $U \supseteq \pi_1(S) \times [0, \tau_0]$ for each $y \in \pi_2(S)$, every $N > 0$ admits $C$ and $R_0$ with
--   $$\|B_R\|_{L^p \to L^q} \le C\|A_R\|_{L^p \to L^q} + CR^{-N} \qquad (R \ge R_0),$$
--   where $A_R$ and $B_R$ have kernels $K_R(x, y)$ and $K_R(x, y)\,b(x, y, 1/R)$.
--
--   This is Lemma 2.1 of T. Tao, *The Bochner–Riesz conjecture implies the restriction conjecture*, Duke Math. J. 96 (1999) 363–375 (preprint p. 4), read with "$b(x, y, \tau)$ is a bounded function which is $C^\infty$ in $x$ and $\tau$" and nothing about the size of its derivatives. A counterexample in dimension $n = 1$, $p = q = 2$: $K_R(x, y) = e^{-2\pi iRxy}$ on $[0, 1]^2$, and $b(x, y, \tau) = e^{2\pi iR_jxy}$ for $y$ in disjoint intervals $I_j$ of length $2^{-j-2}$, with $R_j = 2^{2^j}$. The mission's Lemma 2.1 (`TaoBR.opNorm_le_of_contDiff`) assumes derivative bounds uniform in $y$, which the paper's proof uses.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 4, Lemma 2.1 without derivative bounds uniform in y (printed-fails lemma, not in the paper)

import Mathlib
import Definitions.Def_TaoBR

open MeasureTheory
open scoped ENNReal

namespace TaoBR

theorem not_opNorm_le_of_contDiff_printed :
    ¬ ∀ (n : ℕ) (p q : ℝ≥0∞), 1 ≤ p → 1 ≤ q →
      ∀ (K : ℝ → E n → E n → ℂ) (S : Set (E n × E n)), IsCompact S → ∀ M : ℝ,
      (∀ R, Measurable (Function.uncurry (K R))) →
      (∀ R x y, ‖K R x y‖ ≤ M ∧ (K R x y ≠ 0 → (x, y) ∈ S)) →
      ∀ b : E n → E n → ℝ → ℂ, (∀ τ, Measurable (Function.uncurry fun x y => b x y τ)) →
      ∀ B : ℝ, (∀ x y τ, ‖b x y τ‖ ≤ B) → ∀ τ₀ : ℝ, 0 < τ₀ →
      ∀ U : Set (E n × ℝ), IsOpen U → (Prod.fst '' S) ×ˢ Set.Icc 0 τ₀ ⊆ U →
      (∀ y ∈ Prod.snd '' S, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : E n × ℝ => b z.1 y z.2) U) →
      ∀ N : ℝ, 0 < N → ∃ C R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
        opNorm p q (kernelOp fun x y => K R x y * b x y R⁻¹) ≤
          ENNReal.ofReal C * opNorm p q (kernelOp (K R)) + ENNReal.ofReal (C * R ^ (-N)) := by
  sorry

end TaoBR
