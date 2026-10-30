-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P11_measuredEntropy_lowerSemicontinuous
-- name    : QAlgorithms.Papers.Independent.Bridge50.P11.measuredEntropy_lowerSemicontinuous
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:25:30.7532+00:00
-- url     : https://prove2.me/theorems/a4486573-d2d5-4369-a10c-0ea04bc0e630
-- title:
--   Joint norm lower semicontinuity of measured relative entropy
-- statement:
--   Let $M$ be a $\sigma$-finite von Neumann algebra in standard form on a separable complex Hilbert space. Let $\mu_n,\nu_n,\mu,\nu$ be normal states on $M$ such that $\|\mu_n-\mu\|\to0$ and $\|\nu_n-\nu\|\to0$, where the norm is the norm of the normal functionals. Define $S_{\mathrm{meas}}$ by the supremum over bounded self-adjoint $h\in M$ of $\mu(h)-\log\nu(e^h)$, using natural logarithms. Then
--   $$
--   S_{\mathrm{meas}}(\mu\mid\nu)\le\liminf_{n\to\infty}S_{\mathrm{meas}}(\mu_n\mid\nu_n).
--   $$
--   All entropies take extended-real values. No faithfulness, domination or finiteness assumption is imposed. This gives the limit property used when removing the majorization condition from the recovery inequality.
-- source:
--   Trace- and improved data processing inequalities for von Neumann algebras, arXiv:2102.07479v2, PDF p. 25, Lemma 7

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P11

noncomputable section

open Filter

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Bridge50.P11

open QAlgorithms.Papers.Independent.Claimed50.P06
  (StandardForm IsNormalState IsFaithful IsSigmaFinite vectorFunctional vectorFidelity)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Lemma 7, PDF p.25. Joint lower semicontinuity for the norm of the actual
normal functionals, i.e. their predual norm. The dual operator norm in this
standard representation is precisely that norm. All states, both sequences
and limits, may be nonfaithful, and measured entropies may be infinite. -/
theorem measuredEntropy_lowerSemicontinuous [TopologicalSpace.SeparableSpace H]
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (_form : StandardForm A)
    (_hSigmaFinite : IsSigmaFinite A)
    (mu nu : A →L[ℂ] ℂ) (muSeq nuSeq : ℕ → (A →L[ℂ] ℂ))
    (_hMu : IsNormalState A mu) (_hNu : IsNormalState A nu)
    (_hMuSeq : ∀ n, IsNormalState A (muSeq n))
    (_hNuSeq : ∀ n, IsNormalState A (nuSeq n))
    (_hMuLimit : Tendsto muSeq atTop (nhds mu))
    (_hNuLimit : Tendsto nuSeq atTop (nhds nu)) :
    measuredEntropy A mu nu ≤
      Filter.liminf (fun n => measuredEntropy A (muSeq n) (nuSeq n)) atTop := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P11

end
