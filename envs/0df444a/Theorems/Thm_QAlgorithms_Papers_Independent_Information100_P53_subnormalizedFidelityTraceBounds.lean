-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P53_subnormalizedFidelityTraceBounds
-- name    : QAlgorithms.Papers.Independent.Information100.P53.subnormalizedFidelityTraceBounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:03:54.471546+00:00
-- url     : https://prove2.me/theorems/ba35825d-4247-4d01-8f22-8116df576943
-- title:
--   Lemma 2: subnormalized fidelity and trace norm
-- statement:
--   Let $A,B\succeq0$ act on $\mathbb C^N$, where $N\ge1$, and put $a=\operatorname{Tr}A\le1$, $b=\operatorname{Tr}B\le1$. These operators need not have trace one. Let $F(A,B)=(\operatorname{Tr}|\sqrt A\sqrt B|)^2$ and $\|H\|_1=\operatorname{Tr}|H|$. Then
--
--   $$\frac{\max(a,b)}2-\sqrt{F(A,B)}\ \le\ \frac{\|A-B\|_1}{2}\ \le\ \sqrt{\left(\frac{a+b}{2}\right)^2-F(A,B)}.$$
--
--   This background comparison relates fidelity and trace norm for subnormalized positive operators.
-- source:
--   A Spectrum-Based Converse for Quantum State Discrimination and Its Applications to Classical-Quantum Channel Coding, arXiv:2610.06840v1, PDF p. 3, Lemma 2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P53

open scoped Matrix ComplexConjugate ComplexOrder

open Finset

/-- PDF p.3, Lemma 2 (proof cited to [11], supplementary Eq.(A.11)):
both printed inequalities for subnormalized PSD operators. The lower bound
is max(a,b)/2 - sqrt(F(A,B)), not (a+b)/2 - sqrt(F(A,B)). -/
theorem subnormalizedFidelityTraceBounds {N : ℕ} (hN : 0 < N)
    (A B : Matrix (Fin N) (Fin N) ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (ha : A.trace.re ≤ 1) (hb : B.trace.re ≤ 1) :
    max A.trace.re B.trace.re / 2 - Real.sqrt (fidelity A B) ≤ traceNorm (A - B) / 2 ∧
    traceNorm (A - B) / 2 ≤
      Real.sqrt (((A.trace.re + B.trace.re) / 2) ^ 2 - fidelity A B) := by sorry

end QAlgorithms.Papers.Independent.Information100.P53

end
