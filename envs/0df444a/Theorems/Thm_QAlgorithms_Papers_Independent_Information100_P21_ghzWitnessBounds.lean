-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_ghzWitnessBounds
-- name    : QAlgorithms.Papers.Independent.Information100.P21.ghzWitnessBounds
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:01:20.370976+00:00
-- url     : https://prove2.me/theorems/4427463a-8094-4478-941c-863152343bab
-- title:
--   X.24 — Lemma X.24 (GHZ witnesses). Let βn = D/4 = 2n−2 and αn = D/[2(D − 2)]. The Hermitian operators
-- statement:
--   For $n\ge2$, set $D=2^n$, $\Pi_n=I_D-|0^n\rangle\langle0^n|-|1^n\rangle\langle1^n|$, $\alpha_n=D/[2(D-2)]$, and $\beta_n=D/4$. The Hermitian witnesses are
--   $$Z_s=\alpha_n\Pi_n-\beta_n C_n,\qquad Z_g=Z_s/\beta_n.$$
--   For every fully separable state $\sigma$, $0\le\operatorname{Tr}(Z_s\sigma)\le1$ and $\operatorname{Tr}(Z_g\sigma)\ge0$, while $Z_g\preceq I_D$. The denominator is positive because $n\ge2$.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 29, X.24 — Lemma X.24 (GHZ witnesses). Let βn = D/4 = 2n−2 and αn = D/[2(D − 2)]. The Hermitian operators

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 29, Lemma X.24 (GHZ witnesses). Let βn = D/4 = 2n−2 and αn = D/[2(D − 2)]. The Hermitian operators. -/
theorem ghzWitnessBounds (n : ℕ) (hn : 2≤n) :
  (ghzZ n).IsHermitian ∧ (ghzZg n).IsHermitian ∧
  (∀ sigma : Op (Fin n → Fin 2), sigma∈fs (fun _ : Fin n => 2) →
    0≤(ghzZ n*sigma).trace.re ∧ (ghzZ n*sigma).trace.re≤1 ∧ 0≤(ghzZg n*sigma).trace.re) ∧
  (1-ghzZg n).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
