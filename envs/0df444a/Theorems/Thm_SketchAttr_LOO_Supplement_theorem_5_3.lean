-- Prove2me | Theorems.Thm_SketchAttr_LOO_Supplement_theorem_5_3
-- name    : SketchAttr.LOO.Supplement.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:54:00.825992+00:00
-- url     : https://prove2.me/theorems/de77323e-b405-4ccc-af59-95f6964f32bc
-- title:
--   Theorem 5.3 — oracle lower bound and quadratic stability
-- statement:
--   There are universal constants $\kappa,\varepsilon_0>0$ such that, for every $n\ge1$ and $0<\varepsilon<\varepsilon_0$, any randomized adaptive procedure with worst-case budget $q$ that succeeds uniformly on every real symmetric matrix $A$ with $\|A\|_F\le1/16$,
--
--   $$\Pr_{\mathrm{seed}}\!\left(\max_{i\in[n]}|\widehat L_i-A_{ii}|\le\varepsilon\right)\ge\frac23,$$
--
--   must satisfy
--
--   $$q\ge\kappa\min\{n,\varepsilon^{-1}\}.$$
--
--   Each query permits arbitrary complex $w,g$ and any positive integer $N$, adaptively chosen, and returns $\phi_A(w),\nabla\phi_A(w),D_g\nabla\phi_A(w),\ldots,D_g^N\nabla\phi_A(w)$. The free value and gradient at zero are $(0,0)$. There is no access to the matrix or circuit encoding and no restriction on computation between queries. Complex-valued estimates are permitted.
--
--   The same theorem asserts, for every such symmetric matrix, that $\phi_A(w)=w^\top Aw$ is stable for
--
--   $$\alpha(B)=B^2/16,\qquad\alpha(4)=1.$$
--
--   This companion theorem bounds the black-box query cost; its supporting lower bounds use PSD hard instances, while its input class remains all symmetric matrices.
--
--   Differences from the source:
--   - encoding: indices in [n] and probabilities over random seeds → indices in Fin n and an arbitrary measurable seed probability space; reason: zero-based labels and explicit probability laws change no instance
--   - encoding: sufficiently small positive epsilon and Omega(min(n,epsilon inverse)) queries → universal positive epsilon0 and kappa before all instances, with q at least kappa times min(n,1/epsilon); reason: this quantifies the constants without restricting epsilon to reciprocal integers
--   - encoding: the oracle returns value and gradient derivatives through the chosen degree N, plus free value and gradient at zero → every positive N is allowed and responses are zero-padded after N; the free pair is identically zero for these quadratics; reason: the transcript contains exactly the same information and has no cap on adversarial degree
--   - encoding: maximum absolute error of the estimates against the real diagonal → all Fin n coordinate inequalities with complex norm, allowing complex estimates; reason: finite coordinate inequalities are equivalent to the displayed maximum and include the real estimates
-- source:
--   Chris Liaw, Aranyak Mehta, Grigoris Velegkas, Felix Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (October 2026), PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2, pp. 19–20, Theorem 5.3 and its proof

import Mathlib
import Definitions.Def_SketchAttr_LOO_Supplement_Quadratic

open MeasureTheory
open scoped ENNReal

namespace SketchAttr.LOO.Supplement

theorem theorem_5_3 :
    (∃ κ ε₀ : ℝ, 0 < κ ∧ 0 < ε₀ ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (ε : ℝ), 0 < ε → ε < ε₀ →
      ∀ (Seed : Type) [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
        (q : ℕ) (P : QuadraticProcedure Seed n q),
      (∀ A : RealMatrix n, A.IsSymm → matrixFrobNorm A ≤ 1/16 →
        (2/3 : ℝ≥0∞) ≤ μ {seed | ∀ i : Fin n,
          ‖quadraticEstimate P A seed i - (A i i : ℂ)‖ ≤ ε}) →
      κ * min (n : ℝ) (1/ε) ≤ (q : ℝ)) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ A : RealMatrix n,
      A.IsSymm → matrixFrobNorm A ≤ 1/16 → IsStable (quadratic A) quadraticProfile) ∧
    quadraticProfile ⟨4, by norm_num⟩ = 1 := by sorry

end SketchAttr.LOO.Supplement
