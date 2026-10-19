-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_ghzExactRobustness
-- name    : QAlgorithms.Papers.Independent.Information100.P21.ghzExactRobustness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:02:05.627984+00:00
-- url     : https://prove2.me/theorems/1ed8905c-311e-4eba-ac13-b558e1dc5149
-- title:
--   X.25 — Theorem X.25 (Exact GHZ robustness). For every n ≥ 2,
-- statement:
--   For every $n\ge2$, let $G_n^+$ be the density operator of $(|0^n\rangle+|1^n\rangle)/\sqrt2$. Relative to full separability among the individual qubits,
--   $$R_g^{\mathrm{FS}_n}(G_n^+)=1,\qquad R_s^{\mathrm{FS}_n}(G_n^+)=2^{n-2}.$$
--   The values coincide at $n=2$ and separate for $n\ge3$. The generalized value is credited to Ref. [28]; the paper supplies certificates for both values.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 29, X.25 — Theorem X.25 (Exact GHZ robustness). For every n ≥ 2,

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 29, Theorem X.25 (Exact GHZ robustness). For every n ≥ 2,. -/
theorem ghzExactRobustness (n : ℕ) (hn : 2≤n) :
  fsR (fun _ : Fin n => 2) false (ghz n true)=1 ∧
  fsR (fun _ : Fin n => 2) true (ghz n true)=(2:ℝ)^(n-2) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
