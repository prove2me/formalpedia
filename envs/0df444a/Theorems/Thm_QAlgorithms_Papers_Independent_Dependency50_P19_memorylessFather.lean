-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P19_memorylessFather
-- name    : QAlgorithms.Papers.Independent.Dependency50.P19.memorylessFather
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:15:19.18355+00:00
-- url     : https://prove2.me/theorems/af19e188-5195-4b28-8a6c-50ba574115a9
-- title:
--   Memoryless father for a fixed chosen input
-- statement:
--   All registers are finite dimensional and nonempty, pure sources have unit norm, logarithms and entropies are in bits, and $\|\cdot\|_1$ is the full Schatten trace norm.
--
--   Fix a pure input purification $\psi^{RA}$ and a channel isometry $N:A\to BE$. Put $\phi^{RBE}=(I_R\otimes N)\psi$ and let $\mathcal N=\operatorname{Tr}_E N(\cdot)N^\dagger$. For every $\epsilon,\delta>0$, all sufficiently large $n$ admit an entanglement-assisted code using $\mathcal N^{\otimes n}$, with no backward communication, such that
--
--   $$
--   \log_2 d_{\rm transmitted}\ge n\bigl(\tfrac12 I(R;B)_\phi-\delta\bigr),\qquad
--   \log_2 d_{\rm assistance}\le n\bigl(\tfrac12 I(R;E)_\phi+\delta\bigr).
--   $$
--
--   Independent local CPTP encoding and decoding yield an EPR transmission output within full trace norm $\epsilon$ of the normalized target. The source and channel determine the rates and may determine the block threshold.
--
--   This is the father resource inequality for the chosen input, without an input maximization.
-- source:
--   The mother of all protocols: Restructuring quantum information's family tree, arXiv:quant-ph/0606225v1, PDF p. 14, Section VIII; resource inequality (4)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P19

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section VIII, PDF pp.13–14, resource inequality (4) on p.4.
Rates are for the fixed chosen input; no optimization over inputs is added. -/
theorem memorylessFather {R A B E : Type*}
    [Fintype R] [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq R] [DecidableEq A] [DecidableEq B] [DecidableEq E]
    [Nonempty R] [Nonempty A] [Nonempty B] [Nonempty E]
    (N : Matrix (B × E) A ℂ) (hN : IsIso N)
    (psi : EuclideanSpace ℂ (R × A)) (hpsi : IsState psi) :
    ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N0 : ℕ, ∀ n ≥ N0,
      FatherCode (fun M => traceRight (conjSuperop N M)) n
        (mutualInformation (marginalRA (pureDensity (channelSource N psi)))/2)
        (mutualInformation (marginalRB (pureDensity (channelSource N psi)))/2) eps delta := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P19

end
