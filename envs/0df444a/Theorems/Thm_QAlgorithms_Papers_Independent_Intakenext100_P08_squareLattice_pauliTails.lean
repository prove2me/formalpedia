-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P08_squareLattice_pauliTails
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P08.squareLattice_pauliTails
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:01:30.055427+00:00
-- url     : https://prove2.me/theorems/d64ad097-0106-4621-9160-8e25619a0d84
-- title:
--   Square-lattice residue decoding and independent Pauli tails
-- statement:
--   Let $d\ge2$ be an integer, $\hbar>0$, and $v>0$. Put $\delta=\sqrt{2\pi\hbar/d}$. A real shift $x$ is decoded to the residue $r(x)=\operatorname{round}(x/\delta)\bmod d$. Every shift with $|x|<\delta/2=\sqrt{\pi\hbar/(2d)}$ has residue zero. For independent $q,p\sim N(0,v)$, the residues $r(q),r(p)$ are independent and their nonzero probabilities satisfy
--
--   $$
--   p_X,\ p_Z\le\operatorname{erfc}\left(\sqrt{\frac{\pi\hbar}{4dv}}\right).
--   $$
--
--   On the finite $d$-symbol space the associated operators act as
--
--   $$
--   X|j\rangle=|j+1\bmod d\rangle,\qquad Z|j\rangle=e^{2\pi i j/d}|j\rangle\quad(0\le j<d).
--   $$
--
--   The probabilities can be smaller than the displayed tail because shifts by multiples of $d\delta$ decode to zero. This is a displacement-decoder and finite-operator statement, without an assertion that ideal oscillator combs are normalized states.
-- source:
--   Achievable rates for the Gaussian quantum channel, arXiv:quant-ph/0105058v1, PDF p. 7, §VI, (69)–(71): square-lattice inner decoding and Pauli tail probabilities

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P08

namespace QAlgorithms.Papers.Independent.Intakenext100.P08

open MeasureTheory ProbabilityTheory Matrix

open scoped BigOperators ENNReal

-- Accepted grouped index and source-sign matrix; no paper-local copies.

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)
-- The accepted predicate uses column bases and -sigma: apply it to S.transpose.

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)
-- The accepted pairing has the opposite sign: exchange its two arguments below.

open QAlgorithms.Papers.Independent.Frontier30.P10 (symplecticPair)

/-- PDF p.7, (69)–(71): square-lattice rounded residues, independent Pauli errors,
and their Gaussian upper bounds, together with the finite clock/shift action.
This does not assert a normalizable oscillator realization of the ideal inner code. -/
theorem squareLattice_pauliTails (d : ℕ) (hd : 2 ≤ d) (hbar : ℝ) (hhbar : 0 < hbar)
    (v : NNReal) (hv : 0 < v) :
    let delta := Real.sqrt (2 * Real.pi * hbar / (d : ℝ))
    delta / 2 = Real.sqrt (Real.pi * hbar / (2 * (d : ℝ))) ∧
    (∀ x : ℝ, |x| < delta / 2 → roundedResidue d delta x = 0) ∧
    xErrorProbability d delta v ≤
      complementaryErrorFunction (Real.sqrt (Real.pi * hbar / (4 * (d : ℝ) * (v : ℝ)))) ∧
    zErrorProbability d delta v ≤
      complementaryErrorFunction (Real.sqrt (Real.pi * hbar / (4 * (d : ℝ) * (v : ℝ)))) ∧
    IndepFun (fun x : ℝ × ℝ => roundedResidue d delta x.1)
      (fun x : ℝ × ℝ => roundedResidue d delta x.2)
      ((gaussianReal 0 v).prod (gaussianReal 0 v)) ∧
    (∀ j : Fin d,
      (cyclicX d).mulVec (Pi.single j 1) =
        Pi.single (⟨(j.val + 1) % d, Nat.mod_lt _ (by omega)⟩ : Fin d) 1 ∧
      (cyclicZ d).mulVec (Pi.single j 1) =
        Complex.exp (Complex.I * (2 * Real.pi * (j.val : ℝ) / (d : ℝ) : ℝ)) •
          Pi.single j 1) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P08
