-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P25_sargAcceptance
-- name    : QAlgorithms.Papers.Independent.Gap48.P25.sargAcceptance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:46:19.451861+00:00
-- url     : https://prove2.me/theorems/4aa5ffdb-f4f4-4cd4-886a-ea8f8f450125
-- title:
--   IV.D: SARG04 acceptance and conditional error, Eqs.(53)–(54)
-- statement:
--   Consider the displayed SARG04 example in IV.D, with source clock $\nu_S\ge0$, photon probability $p_A(n)\in[0,1]$, forwarding probability $f_n\in[0,1]$ and channel perturbation $\widetilde\varepsilon_n\in[0,1]$. Bob's bases are equally likely. In the same-basis branch the accepted minus result has probability $\widetilde\varepsilon_n$ and is wrong; in the other-basis branch it has probability $1/2$ and is correct, the assumption of footnote 58. With $\widetilde\nu_S=\nu_S/2$,
--
--   $$R_n=\widetilde\nu_Sp_A(n)f_n(1/2+\widetilde\varepsilon_n),\qquad R_n^w=\widetilde\nu_Sp_A(n)f_n\widetilde\varepsilon_n.$$
--
--   For a nonempty detection class the conditional error is $\varepsilon_n=\widetilde\varepsilon_n/(1/2+\widetilde\varepsilon_n)$. Acceptance is nondecreasing when comparing perturbations in $[0,1]$. This states the source's explicit symmetric example, with its required wrong-basis assumption.
-- source:
--   The Security of Practical Quantum Key Distribution, arXiv:0802.4155v3, PDF p. 32, IV.D: SARG04 acceptance and conditional error, Eqs.(53)–(54)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P25

open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- Eqs.(53)–(54), footnote 58, PDF p.32. Conditional error is asserted only
for a nonempty detection class; both source basis assumptions are in sargAccepted. -/
theorem sargAcceptance (nu pa f e : ℝ) (hnu : 0 ≤ nu)
    (hpa : pa ∈ Set.Icc (0 : ℝ) 1) (hf : f ∈ Set.Icc (0 : ℝ) 1)
    (he : e ∈ Set.Icc (0 : ℝ) 1) :
    sargAccepted nu pa f e = (nu/2)*pa*f*(1/2+e) ∧
    sargWrong nu pa f e = (nu/2)*pa*f*e ∧
    (0 < nu*pa*f → sargWrong nu pa f e/sargAccepted nu pa f e = e/(1/2+e)) ∧
    (∀ e2 : ℝ, e2 ∈ Set.Icc (0 : ℝ) 1 → e ≤ e2 →
      sargAccepted nu pa f e ≤ sargAccepted nu pa f e2) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P25

end
