-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P25_decoyConstraints
-- name    : QAlgorithms.Papers.Independent.Gap48.P25.decoyConstraints
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:41:14.063374+00:00
-- url     : https://prove2.me/theorems/1c28d53c-9fb6-421c-ba8a-32bf7737a2f3
-- title:
--   IV.B.3: common-yield decoy-state constraints, Eq.(32)
-- statement:
--   Let $X$ be a finite nonempty set of random source settings, with probabilities $w_\xi\ge0$ summing to one, source clock $\widetilde\nu_S>0$ and normalized photon laws $p_A(n\mid\xi)$. The conditional $n$-photon signal is the same normalized countable mixture of unit vectors on an arbitrary Hilbert space for every setting. Apply the same detection effect $M$ and wrong-detection subeffect $0\le W\le M\le I$. There exist setting-independent yields $f_n,g_n$ and errors $\varepsilon_n$ with $0\le g_n\le f_n\le1$, $0\le\varepsilon_n\le1$ and $g_n=f_n\varepsilon_n$, such that
--
--   $$R^\xi=\widetilde\nu_S w_\xi\sum_n p_A(n\mid\xi)f_n,\qquad R^\xi Q^\xi=\widetilde\nu_S w_\xi\sum_n p_A(n\mid\xi)g_n.$$
--
--   Here the rates are the actual Born expectation sums; these series are summable. When $R^\xi>0$, $Q^\xi=\sum_n(R_n^\xi/R^\xi)\varepsilon_n$. Zero-frequency settings have zero rates. The equations are linear in detection and error yields; finitely many decoys do not identify every yield exactly. Countable convex mixtures represent full trace-class states, without a finite photon cutoff.
-- source:
--   The Security of Practical Quantum Key Distribution, arXiv:0802.4155v3, PDF p. 29, IV.B.3: common-yield decoy-state constraints, Eq.(32)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P25

open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- Eq.(32), PDF p.29: common conditional states and one fixed instrument give
setting-independent f_n,g_n. Printed linearity in f_n,epsilon_n is expressed
in f_n,g_n=f_n*epsilon_n because wrong counts contain their product. Class rates
use the actual setting clock nu*w xi, converting the source conditional rates.
No claim of exact inference from finitely many settings. -/
theorem decoyConstraints {X H : Type*} [Fintype X] [Nonempty X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (nu : ℝ) (hnu : 0 < nu) (w : X → ℝ)
    (hw : (∀ xi, 0 ≤ w xi) ∧ ∑ xi, w xi = 1) (p : X → PhotonLaw)
    (rho : ℕ → MixedSignal H) (M W : H →L[ℂ] H)
    (hM : M.IsPositive) (hM1 : (1-M).IsPositive) (hW : W.IsPositive)
    (hWM : (M-W).IsPositive) :
    ∃ f g e : ℕ → ℝ,
      (∀ n, f n = signalExpectation (rho n) M ∧
        g n = signalExpectation (rho n) W ∧
        0 ≤ g n ∧ g n ≤ f n ∧ f n ≤ 1 ∧ e n ∈ Set.Icc (0 : ℝ) 1 ∧ g n = f n*e n) ∧
      ∀ xi,
        Summable (decoyComponent nu w p rho M xi) ∧
        Summable (decoyWrong nu w p rho W xi) ∧
        (∑' n, decoyComponent nu w p rho M xi n) = nu*w xi*∑' n, (p xi).mass n*f n ∧
        (∑' n, decoyWrong nu w p rho W xi n) = nu*w xi*∑' n, (p xi).mass n*g n ∧
        (0 < (∑' n, decoyComponent nu w p rho M xi n) →
          (∑' n, decoyWrong nu w p rho W xi n)/(∑' n, decoyComponent nu w p rho M xi n) =
            ∑' n, (decoyComponent nu w p rho M xi n/
              (∑' k, decoyComponent nu w p rho M xi k))*e n) ∧
        (w xi = 0 → (∑' n, decoyComponent nu w p rho M xi n) = 0) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P25

end
