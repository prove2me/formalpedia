-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P31_depolarizingPurities
-- name    : QAlgorithms.Papers.Independent.Support50.P31.depolarizingPurities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:22:48.675912+00:00
-- url     : https://prove2.me/theorems/ed898f95-0f23-44c1-8358-c3146997439c
-- title:
--   Depolarizing products: multiplicativity and explicit purities
-- statement:
--   Let $n\ge1$, let $d_i\ge1$ be the dimensions of complex Hilbert spaces $H_i$, and let $0<p_i<1$. Define the depolarizing channels $\Phi_i(X)=(1-p_i)X+(p_i/d_i)\operatorname{Tr}(X)I_i$, and their actual tensor product $\Phi=\bigotimes_{i=1}^n\Phi_i$. For a channel $\Psi$, write $\nu_p(\Psi)$ for the maximum output Schatten $p$-norm over all density inputs (operator norm when $p=\infty$), and $\nu_{-\infty}(\Psi)$ for the minimum least output eigenvalue, including zero. Then
--   $$
--   \begin{aligned}
--   \nu_2(\Phi)&=\prod_i\nu_2(\Phi_i)
--    =\prod_i\sqrt{\frac{d_i-1}{d_i}(1-p_i)^2+\frac1{d_i}},\\
--   \nu_\infty(\Phi)&=\prod_i\nu_\infty(\Phi_i)
--    =\prod_i\left(1-\frac{p_i(d_i-1)}{d_i}\right),\\
--   \nu_{-\infty}(\Phi)&=\prod_i\nu_{-\infty}(\Phi_i)
--    =\prod_i m_i,\qquad
--   m_i=\begin{cases}1&d_i=1,\\p_i/d_i&d_i>1.\end{cases}
--   \end{aligned}
--   $$
--   These are exact identities for arbitrary density inputs on the joint space, including entangled states.
--
--   **Source correction.** The printed last product uses $p_i/d_i$ in every dimension. A scalar channel is the identity and has least output eigenvalue $1$; the displayed scalar branch corrects that edge without discarding it.
-- source:
--   On some additivity problems in quantum information theory, arXiv:math-ph/0003002v2, PDF p. 11, §5, Theorem (i)-(iii): multiplicativity and explicit depolarizing purities

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P31

noncomputable section

open Filter Asymptotics

open scoped ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P31

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten)

open QAlgorithms.Papers.Independent.Gap48.P03 (holevoQuantity)

open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

open QAlgorithms.Papers.Independent.Dependency50.P44 (tensorChannels)

/-- PDF pp.11–12, final Theorem (i)–(iii), with the p.9 convention.
Printed (iii) is corrected for dimension one: its factor is 1, not p.
All three multiplicativity identities and explicit values are retained. -/
theorem depolarizingPurities {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ) (hd : ∀ i, 0 < d i)
    (p : Fin n → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1) :
    (nuP 2 (depolarizingProduct d hd p) =
        ∏ i, nuP 2 (QuditFidelity.depolarizingMap (d i) (hd i) (p i)) ∧
      (∏ i, nuP 2 (QuditFidelity.depolarizingMap (d i) (hd i) (p i))) =
        ∏ i, Real.sqrt ((((d i : ℝ) - 1) / (d i : ℝ)) * (1 - p i) ^ 2 + 1 / (d i : ℝ))) ∧
    (nuP ⊤ (depolarizingProduct d hd p) =
        ∏ i, nuP ⊤ (QuditFidelity.depolarizingMap (d i) (hd i) (p i)) ∧
      (∏ i, nuP ⊤ (QuditFidelity.depolarizingMap (d i) (hd i) (p i))) =
        ∏ i, (1 - p i * ((d i : ℝ) - 1) / (d i : ℝ))) ∧
    (nuMinus (depolarizingProduct d hd p) =
        ∏ i, nuMinus (QuditFidelity.depolarizingMap (d i) (hd i) (p i)) ∧
      (∏ i, nuMinus (QuditFidelity.depolarizingMap (d i) (hd i) (p i))) =
        ∏ i, if d i = 1 then 1 else p i / (d i : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P31

end
