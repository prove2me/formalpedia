-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P03_classical_entropyAccumulation
-- name    : QAlgorithms.Papers.Independent.Gap20.P03.classical_entropyAccumulation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:15:21.127847+00:00
-- url     : https://prove2.me/theorems/3e57674d-4008-4dbe-97a3-c9ce0a2bebb3
-- title:
--   Theorem 3.1: classical entropy accumulation
-- statement:
--   Let $Z_1,\ldots,Z_n$ have any joint distribution on a finite nonempty alphabet $\mathcal Z$. No independence is assumed. Suppose $h\ge0$ and the Shannon entropy of $Z_i$ conditioned on every supported history $Z_1=z_1,\ldots,Z_{i-1}=z_{i-1}$ is at least $h$. For $0<\lambda<1/2$, define
--   $$\varepsilon=\exp\!\left(-\frac{\lambda^2n}{32[\log_2(|\mathcal Z|/\lambda)]^2}\right).$$
--   Then
--   $$H_\infty^\varepsilon(Z_1\cdots Z_n)\ge(h-2\lambda)n.$$
--   The smoothing is event deletion without renormalization. This accumulates entropy under a per-history lower bound, rather than an average-only assumption.
-- source:
--   A Tight High-Order Entropic Quantum Uncertainty Relation With Applications, arXiv:quant-ph/0612014v2, PDF p. 6, Theorem 3.1: classical entropy accumulation

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

/-- Theorem 3.1, pp.6-7 and Appendix A.1 pp.16-18. No independence assumption;
the entropy hypothesis holds at each supported history. -/
theorem classical_entropyAccumulation {A : Type} [Fintype A] [Nonempty A]
    (n : ℕ) (p : PMF (Fin n → A)) (h : ℝ) (hh : 0 ≤ h)
    (hhistory : ∀ i : Fin n, ∀ v : Fin i.val → A,
      0 < massAt (fun z => p z) (history i) v → h ≤ shannon (nextLaw p i v))
    (lambda : ℝ) (hlambda : 0 < lambda) (hlambdaHalf : lambda < 1/2) :
    (((h-2*lambda)*n : ℝ) : EReal) ≤ smoothJoint (fun z => p z) id
      (accumulationError (Fintype.card A) n lambda) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P03

end
