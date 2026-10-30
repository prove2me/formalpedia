-- Prove2me | Theorems.Thm_TaoBR_opNorm_le_of_contDiff
-- name    : TaoBR.opNorm_le_of_contDiff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:05:37.837894+00:00
-- url     : https://prove2.me/theorems/5ba873f8-a18d-4dd2-ab03-dd63d8354010
-- title:
--   Lemma 2.1 — a smooth bounded factor b(x, y, 1/R) changes the operator norm only by O(R^{−N})
-- statement:
--   Let $1 \le p, q \le \infty$. Let $K_R(x, y)$ ($x, y \in \mathbf R^n$, $R \in \mathbf R$) be measurable kernels with $|K_R| \le M$, all supported in one compact set $S \subseteq \mathbf R^n \times \mathbf R^n$. Let $b(x, y, \tau)$ be complex-valued with $|b| \le B$ and measurable in $(x, y)$ for each $\tau$. Suppose there are $\tau_0 > 0$ and an open set $U \subseteq \mathbf R^n \times \mathbf R$ containing $\pi_1(S) \times [0, \tau_0]$, where $\pi_1$ and $\pi_2$ are the two coordinate projections of $S$, with the following property. For each $y \in \pi_2(S)$, the map $(x, \tau) \mapsto b(x, y, \tau)$ is $C^\infty$ on $U$, with each derivative bounded on $U$ uniformly in $y$. Let $A_R$ and $B_R$ be the operators with kernels $K_R(x,y)$ and $K_R(x,y)\,b(x,y,1/R)$. Then for every $N > 0$ there are $C$ and $R_0$ such that
--   $$\|B_R\|_{L^p \to L^q} \le C\|A_R\|_{L^p\to L^q} + C R^{-N} \qquad (R \ge R_0).$$
--   The operator norms are taken over all $f \in L^p$ (`opNorm`), with values in $[0, \infty]$.
--
--   *Correction.* Read literally, with $b$ only $C^\infty$ in $(x, \tau)$ for each $y$, the lemma is false ([`TaoBR.not_opNorm_le_of_contDiff_printed`](https://prove2.me/theorems/71e24ced-c48a-42fb-900d-92107cfb54dd)). The statement assumes the derivative bounds uniform in $y$ that the proof's expansion uses, in which "the $f_{j,k}$ are uniformly bounded functions" (p. 5).
--
--   *Formalization note.* "$C^\infty$ in $x$ and $\tau$, for $0 \le \tau \lesssim 1$ and $x, y$ in the support of $K$" is read as smoothness on an open neighbourhood of that region. "For each $R \gg 1$" is the threshold $R_0$.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 4, Lemma 2.1

import Mathlib
import Definitions.Def_TaoBR

open scoped ENNReal

namespace TaoBR

theorem opNorm_le_of_contDiff (n : ℕ) (p q : ℝ≥0∞) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (K : ℝ → E n → E n → ℂ) (S : Set (E n × E n)) (hS : IsCompact S) (M : ℝ)
    (hKm : ∀ R, Measurable (Function.uncurry (K R)))
    (hK : ∀ R x y, ‖K R x y‖ ≤ M ∧ (K R x y ≠ 0 → (x, y) ∈ S))
    (b : E n → E n → ℝ → ℂ) (hbm : ∀ τ, Measurable (Function.uncurry fun x y => b x y τ))
    (B : ℝ) (hb : ∀ x y τ, ‖b x y τ‖ ≤ B) (τ₀ : ℝ) (hτ₀ : 0 < τ₀)
    (U : Set (E n × ℝ)) (hU : IsOpen U) (hSU : (Prod.fst '' S) ×ˢ Set.Icc 0 τ₀ ⊆ U)
    (hbsmooth : ∀ y ∈ Prod.snd '' S, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : E n × ℝ => b z.1 y z.2) U)
    (hbder : ∀ k : ℕ, ∃ D : ℝ, ∀ y ∈ Prod.snd '' S, ∀ z ∈ U,
      ‖iteratedFDerivWithin ℝ k (fun z : E n × ℝ => b z.1 y z.2) U z‖ ≤ D) :
    ∀ N : ℝ, 0 < N → ∃ C R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      opNorm p q (kernelOp fun x y => K R x y * b x y R⁻¹) ≤
        ENNReal.ofReal C * opNorm p q (kernelOp (K R)) + ENNReal.ofReal (C * R ^ (-N)) := by
  sorry

end TaoBR
