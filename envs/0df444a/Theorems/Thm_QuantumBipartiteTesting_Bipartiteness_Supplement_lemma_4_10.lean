-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_Supplement_lemma_4_10
-- name    : QuantumBipartiteTesting.Bipartiteness.Supplement.lemma_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:18:15.863256+00:00
-- url     : https://prove2.me/theorems/7e210d91-7748-4c56-b5f7-f47b7afcc324
-- title:
--   Lemma 4.10 — Full rational acceptance identity and uniform feasible error with logarithmic colors
-- statement:
--   Let $c$ be even with $400\ln n\le c\le C_c\ln n$, where $C_c>0$ is fixed. There is an absolute degree constant $C_{\rm deg}>0$. There are $C,\kappa>0$ and an eventual order threshold depending only on $C_c$, before any circuit or grid point, such that every actual finite complex $q$-query circuit has a bivariate polynomial $F$ with
--   $$\deg F\le C_{\rm deg}(1+q\ln(q+2)),\qquad p_{\rm form}(M,\ell)=\frac{F(M,\ell)}{D_q(M,\ell)}.$$
--   This identity holds for all real $\ell\ne0$ away from zeros of the unchanged common denominator. At every feasible integer point of the full grid where this expression is defined,
--   $$p_{\rm feas}(M,\ell)=\frac{F(M,\ell)}{D_q(M,\ell)}+\eta(M,\ell),\qquad |\eta(M,\ell)|\le\exp(Cq\ln n-\kappa n^{1/3}).$$
--   No small-query or tester-correctness hypothesis is imposed. The polynomial is chosen before all evaluations. Rationality and the formal-to-feasible estimate are conclusions. This supplies the unsigned acceptance bound needed for expansion testing.
--
--   Differences from the source:
--   - encoding: vertices [n] and asymptotic notation → Fin n, natural logarithms and explicit uniform constants/thresholds; reason: bijective vertex labeling and logarithm-base changes preserve all source instances
--   - reading: expected acceptance under the formal hard distribution → the published algebraic topology functional, not an overflow-completed probability law; reason: the inherited reading of equations (A.2)–(A.4) is retained; the comparison remains a theorem conclusion
--   - encoding: O(q log q) and a rational expression on its domain → DegreeScale(q)=1+q ln(q+2), with ell nonzero, denominator nonzero, and valid sampling parameters; reason: the scale covers q=0,1 and has the same asymptotic order; the domain excludes only undefined source expressions
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, Lemma 4.10, printed page = PDF page 25; proof p.26

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Supplement_Unsigned

namespace QuantumBipartiteTesting.Bipartiteness.Supplement
open Finset

theorem lemma_4_10 :
    ∃ Cdeg : ℝ, 0 < Cdeg ∧ ∀ Ccol : ℝ, 0 < Ccol →
      ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
        ∀ n ≥ n₀, ∀ c : ℕ, Even c →
          400 * Real.log n ≤ (c : ℝ) → (c : ℝ) ≤ Ccol * Real.log n →
          ∀ k w q : ℕ, ∀ E : Encoding (Fin n) k,
          ∀ A : Algorithm (Address n c) k w q,
          ∀ out : (Address n c × Bits k) × Fin w → Bool,
            ∃ F : Bivariate, (F.totalDegree : ℝ) ≤ Cdeg * DegreeScale q ∧
              (∀ M l : ℝ, l ≠ 0 → Eval (Denominator q) M l ≠ 0 →
                UnsignedFormal E A out M l = Eval F M l / Eval (Denominator q) M l) ∧
              (∀ M l : ℕ, Grid n M l → ValidParameters n M l →
                Eval (Denominator q) M l ≠ 0 →
                ∃ η : ℝ, UnsignedFeasible E A out M l =
                    Eval F M l / Eval (Denominator q) M l + η ∧
                  |η| ≤ Real.exp (C * q * Real.log n - κ * (n : ℝ) ^ (1/3 : ℝ))) := by sorry

end QuantumBipartiteTesting.Bipartiteness.Supplement
