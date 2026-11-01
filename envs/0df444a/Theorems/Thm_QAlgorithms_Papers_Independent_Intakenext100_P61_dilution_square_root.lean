-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P61_dilution_square_root
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P61.dilution_square_root
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:17:29.77558+00:00
-- url     : https://prove2.me/theorems/b4d808b7-df9e-4cf3-8faa-3785bc5d1acf
-- title:
--   Theorem 13: square-root dilution lower bound
-- statement:
--   Fix a normalized finite-dimensional bipartite pure state $\psi$ whose positive Schmidt rank exceeds one and whose reduced state is nonflat on its positive support. There is $\varepsilon_*>0$ (one may choose $\varepsilon_*\le1/1024$) such that, for every fixed $0<\varepsilon<\varepsilon_*$, there are $D>0$, a real sequence $r_n=o(\sqrt n)$ and a threshold $N$ such that every protocol preparing $\psi^{\otimes n}$ from any finite supply of EPR pairs with squared fidelity at least $1-\varepsilon$ has
--
--   $$C\ge D\sqrt n-r_n\qquad(n\ge N).$$
--
--   Both $D$ and the single remainder may depend on $\psi$ and $\varepsilon$, but are chosen before $n$, the EPR supply and the protocol. This gives the square-root dilution obstruction.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, PDF p. 7, Theorem 13: square-root dilution lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P61

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P61

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (supportRank)

open QAlgorithms.Papers.Independent.Bridge50.P40 (entropyInfinity)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

attribute [local instance] Classical.propDecidable

section Dilution

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- PDF pp.6--7, Theorem 13 (statement on p.7): a state-dependent positive
square-root lower bound, with one remainder uniform over all protocols and EPR
counts. The proof's delta<1/2 gives the sufficient error threshold 1/1024. -/
theorem dilution_square_root (psi : EuclideanSpace ℂ (A × B)) (hnorm : ‖psi‖ = 1)
    (hentangled : 1 < supportRank (aliceDensity psi)) (hnonflat : ¬ Flat (aliceDensity psi)) :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧ epsilonStar ≤ 1 / 1024 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonStar →
      ∃ d : ℝ, 0 < d ∧ ∃ r : ℕ → ℝ,
        Asymptotics.IsLittleO Filter.atTop r (fun n : ℕ => Real.sqrt (n : ℝ)) ∧
        ∃ N : ℕ, ∀ n ≥ N, ∀ (k : ℕ) (cost : ℝ),
          QuantumPrepares (eprPairs k) (pureStateCopies psi n) epsilon cost →
          d * Real.sqrt (n : ℝ) - r n ≤ cost := by sorry

end Dilution

end QAlgorithms.Papers.Independent.Intakenext100.P61

end
