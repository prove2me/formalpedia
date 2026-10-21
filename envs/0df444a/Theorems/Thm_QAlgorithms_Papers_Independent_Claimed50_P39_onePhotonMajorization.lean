-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_onePhotonMajorization
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.onePhotonMajorization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:00:34.969682+00:00
-- url     : https://prove2.me/theorems/5fbf71e1-fddd-40de-845b-462b9e714198
-- title:
--   Analytic one-photon majorization
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   For every $n\ge0$, $\mathcal N_n(|0\rangle\langle0|)$ majorizes $\mathcal N_n(|1\rangle\langle1|)$, meaning that each ordered partial sum of the latter is at most the former's
--   $$T_q=1-\left(\frac n{n+1}\right)^{q+1}\quad(q\in\mathbb N).$$
--   For $n>0$ let $w_i=n^i(n+i/n)/(n+1)^{i+2}$ be the photon-indexed one-photon output weights. The ordered sums are
--   $$A_q=1-\left(1+\frac{q+1}{n(n+1)}\right)\left(\frac n{n+1}\right)^{q+1}$$
--   when $w_0>w_{q+1}$, and otherwise are
--   $$B_q=1-\left(1+\frac{q+2}{n(n+1)}\right)\left(\frac n{n+1}\right)^{q+2}-\frac n{(n+1)^2}.$$
--   For $n\ge1$ they always equal $A_q$; the two formulas agree at insertion ties. Zero noise is handled by the identity channel.
--
--   This is an analytic result for one photon, without a claim for arbitrary Fock inputs.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 10, §VI.A, Eqs.(68), (71)–(72): analytic one-photon case

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF pp.9–10, Eqs.(68),(71)–(72): analytic one-photon majorization only.
The insertion regime compares explicit eigenvalues, rather than guessing a
small-q cutoff. n=0 is the identity and is covered without a quotient. -/
theorem onePhotonMajorization (n : ℝ) (hn : 0 ≤ n) :
    Majorizes (displacementNoiseChannel n (B.fockDyad 0 0)) (displacementNoiseChannel n (B.fockDyad 1 1)) ∧
    (∀ q : ℕ, partialSum (displacementNoiseChannel n (B.fockDyad 0 0)) q = 1 - (n / (n + 1)) ^ (q + 1)) ∧
    (0 < n → ∀ q : ℕ, partialSum (displacementNoiseChannel n (B.fockDyad 1 1)) q =
      if onePhotonWeight n 0 ≤ onePhotonWeight n (q + 1) then onePhotonSumB n q
      else onePhotonSumA n q) ∧
    (1 ≤ n → ∀ q : ℕ, partialSum (displacementNoiseChannel n (B.fockDyad 1 1)) q = onePhotonSumA n q) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
