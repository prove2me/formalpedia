-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P61_residual_family_cost
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P61.residual_family_cost
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:22:28.253383+00:00
-- url     : https://prove2.me/theorems/6477b36e-d9e2-4f10-86f3-1c64c2a77dde
-- title:
--   §IV, unnumbered: Lo–Popescu residual states have large communication cost
-- statement:
--   Fix a normalized bipartite pure state $\psi$ with positive Schmidt rank greater than one and nonflat positive spectrum, and write $E=S(\psi_A)$ in bits. For every sufficiently small fixed error $\varepsilon>0$, there exist constants $K,D>0$, a threshold $N$, Bell counts $m_n$, positive local residual dimensions $a_n,b_n$, normalized residual vectors $\chi_n$, and separate local isometric embeddings $U_n,V_n$ such that for $n\ge N$,
--
--   $$|m_n-nE|\le K\sqrt n,\quad\log_2 a_n,\log_2 b_n,E(\chi_n)\le K\sqrt n,$$
--   $$F\bigl((U_n\otimes V_n)(\mathrm{EPR}^{\otimes m_n}\otimes\chi_n),\psi^{\otimes n}\bigr)\ge1-\varepsilon.$$
--
--   Every deterministic quantum protocol preparing $\chi_n$ from any finite EPR supply with squared fidelity at least $1-\varepsilon$ has $C\ge D\sqrt n$. All witnesses precede $n$ and the preparation protocol. The factorization is credited by the source to Lo–Popescu [17]; the cost conclusion is the present paper's application.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, PDF p. 8, §IV, unnumbered: Lo–Popescu residual states have large communication cost

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P61

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P61

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (supportRank)

open QAlgorithms.Papers.Independent.Bridge50.P40 (entropyInfinity)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

attribute [local instance] Classical.propDecidable

/-- PDF p.6, (20), and p.8: Lo--Popescu residual-family witnesses and their
entropy and preparation-cost bounds. The factorization credited to [17] is
expressed in reverse as local isometric embeddings of Bell pairs and the small
residual into the original registers; unused ambient basis vectors are irrelevant.
Neither the cost lower bound nor the factorization is assumed as a structure field. -/
theorem residual_family_cost {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (psi : EuclideanSpace ℂ (A × B)) (hnorm : ‖psi‖ = 1)
    (hentangled : 1 < supportRank (aliceDensity psi)) (hnonflat : ¬ Flat (aliceDensity psi)) :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧ epsilonStar ≤ 1 / 4096 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonStar →
      ∃ K d : ℝ, 0 < K ∧ 0 < d ∧ ∃ N : ℕ,
      ∃ (m rA rB : ℕ → ℕ)
        (chi : ∀ n, EuclideanSpace ℂ (Fin (rA n) × Fin (rB n)))
        (U : ∀ n, Matrix (Fin n → A) (Fin (2 ^ m n) × Fin (rA n)) ℂ)
        (V : ∀ n, Matrix (Fin n → B) (Fin (2 ^ m n) × Fin (rB n)) ℂ),
      ∀ n ≥ N,
        0 < rA n ∧ 0 < rB n ∧ ‖chi n‖ = 1 ∧
        |(m n : ℝ) - (n : ℝ) * entropyOne (aliceDensity psi)| ≤ K * Real.sqrt (n : ℝ) ∧
        logTwo (rA n) ≤ K * Real.sqrt (n : ℝ) ∧
        logTwo (rB n) ≤ K * Real.sqrt (n : ℝ) ∧
        entropyOne (aliceDensity (chi n)) ≤ K * Real.sqrt (n : ℝ) ∧
        (U n)ᴴ * U n = 1 ∧ (V n)ᴴ * V n = 1 ∧
        fidelity (pureDensity (applyLocalMaps (U n) (V n) (tensorPureStates (eprPairs (m n)) (chi n))))
          (pureDensity (pureStateCopies psi n)) ≥ 1 - epsilon ∧
        ∀ (k : ℕ) (cost : ℝ), QuantumPrepares (eprPairs k) (chi n) epsilon cost →
          d * Real.sqrt (n : ℝ) ≤ cost := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P61

end
