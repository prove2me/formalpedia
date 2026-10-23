-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P15_degradation_additivity
-- name    : QAlgorithms.Papers.Independent.Gap20.P15.degradation_additivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:22:34.761671+00:00
-- url     : https://prove2.me/theorems/44a80565-7a4f-4187-af3e-0e628f934643
-- title:
--   Lemma 3: degradation additivity
-- statement:
--   Let $N:A\to B$ and $D:B\to E$ be completely positive trace-preserving maps on the full trace class of nonzero separable complex Hilbert spaces. Let $G$ be a nonnegative discrete spectral energy observable with ground energy zero and $\operatorname{Tr}e^{-\beta G}<\infty$ for every $\beta>0$. Fix a finite $W\ge0$. Assume Condition 7: one finite bound on $H(N(\rho))$ holds uniformly over all normalized states with $\operatorname{Tr}(G\rho)\le W$. Entropies are in bits.
--
--   Define $U_D(N,G,W)=\sup_{\rho:\operatorname{Tr}(G\rho)\le W}[H(N(\rho))-H(DN(\rho))]$, interpreting an individual entropy difference as $-\infty$ when the degraded output entropy is infinite. For every integer $n\ge1$, put $G_n=n^{-1}\sum_{j=1}^nG_j$. Then
--
--   $$U_{D^{\otimes n}}(N^{\otimes n},G_n,W)=n\,U_D(N,G,W).$$
--
--   The optimization includes entangled inputs and imposes average energy across uses. It supplies the entropy optimization in the approximate-degradability bounds.
-- source:
--   Bounding the energy-constrained quantum and private capacities of phase-insensitive bosonic Gaussian channels, arXiv:1708.07257v3, PDF p. 16, Lemma 3

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P15

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P15

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Hamiltonian)

open QAlgorithms.Papers.Independent.Gap48.P26 (entropyBits)

open QAlgorithms.Papers.Independent.Claimed50.P35 (traceClassChannelPower)

open scoped ENNReal

/-- Lemma 3, PDF pp.16-17, (4.3). Genuine trace-class channels on nonzero
separable spaces, Gibbs input energy, and standing Condition 7. Values may be
minus infinity when D creates infinite entropy. No finiteness of D is added. -/
theorem degradation_additivity
    {I J E : Type} [Countable I] [Countable J] [Countable E]
    [Nonempty I] [Nonempty J] [Nonempty E]
    (N : Channel I J) (D : Channel J E) (H : Hamiltonian I)
    (hnonnegative : ∀ i, 0 ≤ H.energy i)
    (hground : ∃ i, H.energy i = 0) (hgibbs : H.gibbs)
    (budget : ℝ) (hbudget : 0 ≤ budget)
    (houtput : finiteOutputEntropy N H.energy budget)
    (n : ℕ) (hn : 1 ≤ n) :
    degradationSupremum (traceClassChannelPower N.val n)
      (traceClassChannelPower D.val n) (averageSpectrum H.energy n) budget =
      (n : EReal) * degradationSupremum N.val D.val H.energy budget := by sorry

end QAlgorithms.Papers.Independent.Gap20.P15

end
