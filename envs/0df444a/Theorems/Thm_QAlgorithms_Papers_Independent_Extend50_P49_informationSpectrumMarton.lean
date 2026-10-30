-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P49_informationSpectrumMarton
-- name    : QAlgorithms.Papers.Independent.Extend50.P49.informationSpectrumMarton
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:25:41.764475+00:00
-- url     : https://prove2.me/theorems/0f7d1512-72ef-4b9c-9159-89cf5b09f88d
-- title:
--   Information-spectrum classical-quantum Marton inner bound
-- statement:
--   Fix finite single-letter alphabets $X,U,V$ and nonzero finite-dimensional systems $B,C$. For every $n\ge1$, let $N^{(n)}:X^n\to\mathcal S(B^{\otimes n}\otimes C^{\otimes n})$ be an arbitrary classical-quantum broadcast channel, let $p_{U^nV^n}$ be a normalized joint law, and let $f_n:U^n\times V^n\to X^n$ be deterministic. Compute the joint cq state from these data by equation (4) at block length $n$ and take its actual $U^nB^n$ and $V^nC^n$ marginals. No memorylessness, independence, or identical distribution across blocks is imposed.
--   For the $U,B$ sequence define the spectral inf rate as the extended supremum of real $\gamma$ for which
--   $$\lim_{n\to\infty}\sum_u p_{U^n}(u)\operatorname{Tr}\!\left[\{\rho_{B^n\mid u}-2^{n\gamma}\rho_{B^n}>0\}\rho_{B^n\mid u}\right]=1,$$
--   where braces denote the strictly positive spectral projector. Define $\underline I(V;C)$ in the same way. Define the spectral sup rate by
--   $$\overline I(U;V)=\inf\left\{\lambda:\lim_{n\to\infty}\Pr\!\left[\frac1n\log_2\frac{p_{U^nV^n}(U^n,V^n)}{p_{U^n}(U^n)p_{V^n}(V^n)}>\lambda\right]=0\right\}.$$
--   All these extrema are extended; for the stated fixed finite base alphabets and output dimensions their actual rates are finite. Let $R_1,R_2\ge0$ satisfy
--   $$R_1<\underline I(U;B),\qquad R_2<\underline I(V;C),\qquad R_1+R_2<\underline I(U;B)+\underline I(V;C)-\overline I(U;V).$$
--   Then there are positive integer message counts $M_i(n)$, deterministic block encoders, and separate fixed block POVMs at every positive block length such that
--   $$\lim_{n\to\infty}P_{\rm joint\ error}(n)=0,\qquad R_i\le\liminf_{n\to\infty}\frac{\log_2M_i(n)}n\quad(i=1,2).$$
--   Here the error is averaged over independent uniform private messages. This is achievability along the full sequence of general block channels.
--
--   **Formalization Note** The conditional state inside the first trace corrects the printed marginal in Definition 9. Unnormalized cq blocks implement this convention without dividing by zero-probability auxiliary symbols. Positive lengths are indexed as $n=k+1$; eventual lower bounds for every positive rate backoff express the liminf constraints without a real-valued unbounded infimum default.
-- source:
--   One-shot Marton inner bound for classical-quantum broadcast channel, arXiv:1410.3248v5, PDF p. 17, Theorem 6; corrected Definition 9

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P49

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P49

open QAlgorithms MeasureTheory Filter

open scoped BigOperators Matrix ComplexOrder Topology

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 6, PDF p.17: full information-spectrum cq Marton inner bound.
Arbitrary block channels and correlated auxiliary sequences; no iid hypothesis.
The quantities use corrected Definition 9 (see spectralAcceptance).
All spectra here are finite: fixed finite base alphabets and fixed finite local
output dimensions give uniform per-letter information bounds. -/
theorem informationSpectrumMarton {X U V B C : Type}
    [Fintype X] [Fintype U] [Fintype V] [Fintype B] [Fintype C]
    (N : (k : ℕ) → CqChannel (PositiveBlockWord X k) (PositiveBlockWord B k) (PositiveBlockWord C k))
    (p : (k : ℕ) → AuxiliaryLaw (PositiveBlockWord U k × PositiveBlockWord V k))
    (f : (k : ℕ) → PositiveBlockWord U k → PositiveBlockWord V k → PositiveBlockWord X k)
    (R1 R2 : ℝ) (hR1 : 0 ≤ R1) (hR2 : 0 ≤ R2)
    (hBob : (R1 : EReal) < spectralInfMutualInformation (fun k => inducedUB (N k) (p k) (f k)))
    (hCharlie : (R2 : EReal) < spectralInfMutualInformation (fun k => inducedVC (N k) (p k) (f k)))
    (hSum : ((R1 + R2 : ℝ) : EReal) <
      spectralInfMutualInformation (fun k => inducedUB (N k) (p k) (f k)) +
      spectralInfMutualInformation (fun k => inducedVC (N k) (p k) (f k)) - spectralSupMutualInformation p) :
    SpectrumAchievable N R1 R2 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P49

end
