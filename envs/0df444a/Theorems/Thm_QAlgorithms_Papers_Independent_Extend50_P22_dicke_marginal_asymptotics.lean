-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_dicke_marginal_asymptotics
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.dicke_marginal_asymptotics
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:20:29.116979+00:00
-- url     : https://prove2.me/theorems/507925f9-c944-47f0-97a2-81279f490288
-- title:
--   Lemma 14: fixed-magnetization marginal fidelity asymptotics
-- statement:
--   Fix a number $d\ge0$ of spins and an even integer magnetization $m$. Let $\rho_d^{m,m}(N)$ be the $d$-site marginal of the normalized $N$-spin Dicke state of magnetization $m$, and define the zero-magnetization marginal similarly. Their common Dicke-basis probabilities are the hypergeometric weights in (D.60); root fidelity is the sum of the square roots of corresponding probability products. There exist $D\in\mathbb R$, $C\ge0$ and $N_0>0$, depending on $d,m$ only, such that every even $N\ge N_0$ is admissible and $$F(\rho_d^{m,m}(N),\rho_d^{0,0}(N))\ge1-\frac D{N^2}-\frac C{N^3}.$$ This retains the asymptotic lower bound without choosing an unsupported leading coefficient.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 50, Lemma 14: fixed-magnetization marginal fidelity asymptotics

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF pp.50–52, Lemma 14, (D.65). d,m fixed; constants precede even N.
A lower signed O(N^-3) is expressed by subtracting C/N^3, with no invented leading coefficient. -/
theorem dicke_marginal_asymptotics (d : ℕ) (m : ℤ) (hm : Even m) :
    ∃ D : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ, 0 < N0 ∧
      ∀ N ≥ N0, Even N → d ≤ N ∧ m.natAbs ≤ N ∧
        1 - D / (N : ℝ) ^ 2 - C / (N : ℝ) ^ 3 ≤ dickeMarginalRootFidelity N d m := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
