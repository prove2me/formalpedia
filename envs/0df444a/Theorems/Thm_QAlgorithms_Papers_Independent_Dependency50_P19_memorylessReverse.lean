-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P19_memorylessReverse
-- name    : QAlgorithms.Papers.Independent.Dependency50.P19.memorylessReverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:16:12.926128+00:00
-- url     : https://prove2.me/theorems/3a9a7d7c-0340-4e02-a1ff-e15fe575ee3d
-- title:
--   Source-relative memoryless feedback reverse Shannon
-- statement:
--   All registers are finite dimensional and nonempty, pure sources have unit norm, logarithms and entropies are in bits, and $\|\cdot\|_1$ is the full Schatten trace norm.
--
--   Fix a pure input purification $\psi^{RA}$ and an isometry $N:A\to BE$, and define $\phi^{RBE}=(I_R\otimes N)\psi$. For every $\epsilon,\delta>0$, all sufficiently large $n$ admit a local CPTP encoder and decoder using a shared normalized EPR state and one forward message $Q$, such that
--
--   $$
--   \log_2 d_Q\le n\bigl(\tfrac12 I(R;B)_\phi+\delta\bigr),\qquad
--   \log_2 d_{\rm EPR}\le n\bigl(\tfrac12 I(B;E)_\phi+\delta\bigr).
--   $$
--
--   On the specified source $\psi^{\otimes n}$ the final joint state is within full trace norm $\epsilon$ of $\phi^{\otimes n}$. The reference remains untouched, Alice receives $E^n$, and Bob receives $B^n$.
--
--   This is feedback simulation relative to one memoryless source; it makes no worst-case diamond-norm claim.
-- source:
--   The mother of all protocols: Restructuring quantum information's family tree, arXiv:quant-ph/0606225v1, PDF p. 11, Eq. (33); Section IX, p.14

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P19

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Eq.(33), PDF p.11, asserted achievable in Section IX, p.14.
This is memoryless source-relative feedback simulation, not a diamond-norm assertion. -/
theorem memorylessReverse {R A B E : Type*}
    [Fintype R] [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq R] [DecidableEq A] [DecidableEq B] [DecidableEq E]
    [Nonempty R] [Nonempty A] [Nonempty B] [Nonempty E]
    (N : Matrix (B × E) A ℂ) (hN : IsIso N)
    (psi : EuclideanSpace ℂ (R × A)) (hpsi : IsState psi) :
    ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N0 : ℕ, ∀ n ≥ N0,
      ReverseCode N psi n
        (mutualInformation (marginalRA (pureDensity (channelSource N psi)))/2)
        (mutualInformation (traceLeft (pureDensity (channelSource N psi)))/2) eps delta := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P19

end
