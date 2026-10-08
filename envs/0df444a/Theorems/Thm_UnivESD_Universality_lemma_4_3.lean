-- Prove2me | Theorems.Thm_UnivESD_Universality_lemma_4_3
-- name    : UnivESD.Universality.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:33.38695+00:00
-- url     : https://prove2.me/theorems/d0a0366b-5f39-457d-8a43-e8f62b1b2b0c
-- title:
--   Lemma 4.3 (low-dimensional contribution): $\frac1n\sum_{i\le(1-\delta)n}(\log\mathrm{dist}(\frac{X_i}{\sqrt n},V_i)-\log\mathrm{dist}(\frac{Y_i}{\sqrt n},W_i))=O(\varepsilon)$
-- statement:
--   Work in the setting of §4 (after the shift $z=0$): $x,y$ have zero mean and unit variance, $M_n$ satisfies (1.3) and (4.2), the ESDs $\mu_{\frac1nM_nM_n^*}$ converge, $A_n=M_n+X_n$, $B_n=M_n+Y_n$. Let $X_i$ (resp. $Y_i$) be the rows of $A_n$ (resp. $B_n$), $V_i=\mathrm{span}(X_1,\dots,X_{i-1})$, $W_i=\mathrm{span}(Y_1,\dots,Y_{i-1})$. Then for every $\varepsilon>0$ there exists $0<\delta<1/2$ such that, with probability $1-O(\varepsilon)$,
--   $$\frac1n\sum_{1\le i\le(1-\delta)n}\Bigl(\log\mathrm{dist}\Bigl(\frac1{\sqrt n}X_i,V_i\Bigr)-\log\mathrm{dist}\Bigl(\frac1{\sqrt n}Y_i,W_i\Bigr)\Bigr)=O(\varepsilon)$$
--   for all but finitely many $n$.
--
--   This is the comparison of the first $(1-\delta)n$ rows, where the two ensembles are matched through the limiting singular value distribution (Dozier–Silverstein).
--
--   **Formalization Note.** Both $O(\varepsilon)$ are $C\varepsilon$ with one constant $C$ fixed before $\varepsilon$; "with probability $1-O(\varepsilon)$" is "the exceptional event has probability at most $C\varepsilon$". Because $\log 0=0$ in Lean, the event also requires every distance in the range to be positive. The standing assumptions of §4 — (1.3), (4.2) and convergence of $\mu_{\frac1nM_nM_n^*}$ (which is (1.4) at $z=0$) — are hypotheses. The page calls $Y_i$ "the rows of $\frac1{\sqrt n}B_n$" and then normalizes again; here $Y_i$ are the rows of $B_n$, consistent with $V_i$ and with Lemma 4.2. Indices are one-based in the inequalities.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, p. 2045 (PDF 23), Lemma 4.3; setting p. 2043–2044 (PDF 21–22)

import Mathlib
import Definitions.Def_UnivESD_Universality_Basic
import Definitions.Def_UnivESD_Universality_Model

open MeasureTheory Filter Topology

namespace UnivESD.Universality

/-- Lemma 4.3 (low-dimensional contribution), p. 2045, in the setting of §4 (`z = 0`, (1.3),
the row normalization (4.2), and convergence of the ESDs of `(1/n) M_n M_n^*`). -/
theorem lemma_4_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (xs ys : ℕ → ℕ → Ω → ℂ) (hx : IsIIDArray P xs) (hy : IsIIDArray P ys)
    (M : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (hM : ShiftBound M)
    (h42 : ∃ K : ℝ, ∀ n (i : Fin n), (n : ℝ) ≤ 2 * ((i : ℕ) + 1 : ℝ) →
      ‖row (M n) i‖ ≤ K * Real.sqrt n)
    (hMM : ESDConverges (shiftedGram M 0)) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
      P {ω | ¬ ∀ᶠ n : ℕ in atTop,
        (∀ i : Fin n, ((i : ℕ) + 1 : ℝ) ≤ (1 - δ) * n →
          0 < rowDist (invSqrt n • (M n + cornerMatrix xs n ω)) i ∧
            0 < rowDist (invSqrt n • (M n + cornerMatrix ys n ω)) i) ∧
        |(1 / (n : ℝ)) * ∑ i ∈ Finset.univ.filter (fun i : Fin n =>
            ((i : ℕ) + 1 : ℝ) ≤ (1 - δ) * n),
          (Real.log (rowDist (invSqrt n • (M n + cornerMatrix xs n ω)) i) -
            Real.log (rowDist (invSqrt n • (M n + cornerMatrix ys n ω)) i))| ≤ C * ε}
        ≤ ENNReal.ofReal (C * ε) := by sorry

end UnivESD.Universality
