-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_arbitraryOutputRepresentation
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.arbitraryOutputRepresentation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:01:44.375393+00:00
-- url     : https://prove2.me/theorems/c87f04b5-11a9-43ec-9602-cf61a721e8f6
-- title:
--   Arbitrary pure-input Fock representation
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   Let $u=(u_j)_{j\ge0}\in\ell^2$ have norm one. For $n>0$ and integers $k,\ell\ge0$,
--   $$\langle k+\ell|\mathcal N_n(|u\rangle\langle u|)|k\rangle=
--   \sqrt{\frac{k!}{(k+\ell)!}}\sum_{j=0}^\infty\sqrt{\frac{j!}{(j+\ell)!}}u_{j+\ell}\overline{u_j}\frac{(j+k+\ell)!}{j!k!}\frac{n^{j+k}}{(1+n)^{j+k+\ell+1}}F_{j,k,\ell}(1-n^{-2}),$$
--   where
--   $$F_{j,k,\ell}(z)=\sum_{r=0}^{\min(j,k)}\frac{(-j)_r(-k)_r}{(-(j+k+\ell))_r r!}z^r,\qquad(x)_r=\prod_{s=0}^{r-1}(x+s).$$
--   The complete coefficient series converges to that matrix entry and the output is a density. At $n=0$ the output is $|u\rangle\langle u|$ separately. No absolute-summability assumption on the amplitudes is imposed.
--
--   The terminating polynomial removes the singular general-parameter hypergeometric interpretation.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 11, §VI.B, Eq.(77), Appendix E, Eq.(E5)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF pp.10–11,14–15, Eq.(77)/E5: arbitrary normalized l2 pure input.
HasSum guards the complete infinite j-series. No l1-amplitude or photon-cutoff
hypothesis is imposed. At zero noise the channel is the identity separately. -/
theorem arbitraryOutputRepresentation (n : ℝ) (hn : 0 ≤ n) (u : B.Fock) (hu : ‖u‖ = 1) :
    B.IsDensity (displacementNoiseChannel n (pureState u)) ∧
    (0 < n → ∀ k ell : ℕ, HasSum (outputTerm n u k ell)
      (displacementNoiseChannel n (pureState u) (B.fockKet k) (k + ell))) ∧
    (n = 0 → displacementNoiseChannel n (pureState u) = pureState u) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
