-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P61_exact_dilution_linear
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P61.exact_dilution_linear
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:16:19.522267+00:00
-- url     : https://prove2.me/theorems/a1789765-5278-47df-8cee-18de35649c22
-- title:
--   §II, unnumbered: linear exact dilution lower bound
-- statement:
--   Fix complex amplitudes $\alpha,\beta$ with $|\alpha|^2+|\beta|^2=1$, $0<|\alpha|^2<1$, and $|\alpha|^2\ne1/2$. Write $\psi=\alpha|00\rangle+\beta|11\rangle$. There are constants $c>0$ and $N$ such that, for every $n\ge N$, every supply of EPR pairs and every exact deterministic quantum protocol producing $\psi^{\otimes n}$, its communication cost satisfies
--
--   $$C\ge c n.$$
--
--   The constants may depend on the fixed amplitudes, and precede the block size and protocol. This is the linear exact-error contrast to approximate dilution.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, PDF p. 3, §II, unnumbered: linear exact dilution lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P61

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P61

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (supportRank)

open QAlgorithms.Papers.Independent.Bridge50.P40 (entropyInfinity)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

attribute [local instance] Classical.propDecidable

/-- PDF p.3, unnumbered exact dilution bound: nonzero unequal Schmidt weights.
The asymptotic constants precede n, the EPR supply and every protocol. -/
theorem exact_dilution_linear (alpha beta : ℂ)
    (hnorm : Complex.normSq alpha + Complex.normSq beta = 1)
    (hpositive : 0 < Complex.normSq alpha) (hbelow : Complex.normSq alpha < 1)
    (hnonflat : Complex.normSq alpha ≠ 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ (k : ℕ) (cost : ℝ),
      Quantum (pureDensity (eprPairs k)) (pureDensity (pureStateCopies (binaryState alpha beta) n)) cost →
      c * (n : ℝ) ≤ cost := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P61

end
