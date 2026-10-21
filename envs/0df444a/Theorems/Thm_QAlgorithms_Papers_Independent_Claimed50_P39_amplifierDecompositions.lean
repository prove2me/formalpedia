-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_amplifierDecompositions
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.amplifierDecompositions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:02:33.26319+00:00
-- url     : https://prove2.me/theorems/41529757-8a01-4308-bbb4-e56012381e9e
-- title:
--   Finite-gain amplifier factorizations
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   For intensity gain $\kappa\ge1$, let $\mathcal A_\kappa$ be the quantum-limited amplifier constructed using amplitude parameter $\sqrt\kappa$. It is a normal CPTP map with actual trace-norm Kraus sums and
--   $$\chi_{\mathcal A_\kappa(\rho)}(z)=\chi_\rho(\sqrt\kappa z)e^{-(\kappa-1)|z|^2/2}.$$
--   For $0<t<1$, $t\le\eta\le1$, $N\ge0$ and $(1-\eta)N+t-\eta\ge0$,
--   $$\mathcal E_\eta^N=\mathcal E_t^{[(1-\eta)N+t-\eta]/(1-t)}\circ\mathcal A_{\eta/t}.$$
--   Also,
--   $$\mathcal N_n=\mathcal E_{1-n}^0\circ\mathcal A_{1/(1-n)}\quad(0\le n<1),$$
--   $$\mathcal N_{(1-\eta)/\eta}=\mathcal A_{1/\eta}\circ\mathcal E_\eta^0\quad(0<\eta\le1),$$
--   $$\mathcal N_n=\mathcal E_{1-t}^{(n-t)/t}\circ\mathcal A_{1/(1-t)}\quad(0<t<1,\ t\le n).$$
--   All channel identities hold on every density. The excluded singular endpoints do not denote infinite-gain channels.
--
--   These are the finite factorizations used in the paper's entropy comparisons.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 12, Appendix B, Eqs.(B2)–(B7): amplifier factorization

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- Appendix B, PDF p.12, Eqs.(B2)–(B7): finite-gain factorizations.
Intensity gain is kappa; the accepted Kraus parameter is sqrt(kappa).
The singular decompositions n=1 and t=0,1 are not finite channel identities. -/
theorem amplifierDecompositions :
    (∀ kappa : ℝ, 1 ≤ kappa →
      B.AmplifierRealized (Real.sqrt kappa) ∧ IsNormalFockChannel (amplifier kappa) ∧
      ∀ X : B.FockOperator, B.IsDensity X → B.IsDensity (amplifier kappa X) ∧
        B.TraceHasSum (fun j => B.krausTerm (B.amplifierKraus (Real.sqrt kappa) j) X)
          (amplifier kappa X) ∧
        ∀ z : ℂ, B.characteristic (amplifier kappa X) z =
          B.characteristic X ((Real.sqrt kappa : ℂ) * z) *
            (Real.exp (-(kappa - 1) * Complex.normSq z / 2) : ℂ)) ∧
    (∀ eta t N : ℝ, 0 < t → t < 1 → t ≤ eta → eta ≤ 1 → 0 ≤ N →
      0 ≤ (1 - eta) * N + t - eta → ∀ X, B.IsDensity X →
        thermal eta N X = thermal t (((1 - eta) * N + t - eta) / (1 - t)) (amplifier (eta / t) X)) ∧
    (∀ n : ℝ, 0 ≤ n → n < 1 → ∀ X, B.IsDensity X →
      displacementNoiseChannel n X = thermal (1 - n) 0 (amplifier (1 / (1 - n)) X)) ∧
    (∀ eta : ℝ, 0 < eta → eta ≤ 1 → ∀ X, B.IsDensity X →
      displacementNoiseChannel ((1 - eta) / eta) X = amplifier (1 / eta) (thermal eta 0 X)) ∧
    (∀ n t : ℝ, 0 < t → t < 1 → t ≤ n → ∀ X, B.IsDensity X →
      displacementNoiseChannel n X = thermal (1 - t) ((n - t) / t) (amplifier (1 / (1 - t)) X)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
