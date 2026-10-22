-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P30_channel_factorization
-- name    : QAlgorithms.Papers.Independent.Gap48.P30.channel_factorization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:15:38.358991+00:00
-- url     : https://prove2.me/theorems/fa9a60f0-6902-4228-af76-9232c5b91a08
-- title:
--   Loss followed by amplification realizes every phase-insensitive channel
-- statement:
--   Let $\tau\ge0$ and $\nu\ge|\tau-1|$. The one-mode Gaussian channel $M_{\tau,\nu}$ has $K=\sqrt{\tau}I$, $N=\nu I$, and vacuum covariance $I$. Define
--
--   $$
--   G=\frac{\tau+\nu+1}{2},\qquad T=\frac{2\tau}{\tau+\nu+1}.
--   $$
--
--   Then $G\ge1$, $0\le T\le1$, $\tau=TG$ and $\nu=G(1-T)+(G-1)$. If $L_T$ denotes loss of intensity transmissivity $T$ with vacuum environment and $A_G$ denotes the vacuum-environment amplifier of intensity gain $G$, then
--
--   $$
--   M_{\tau,\nu}(\rho)=A_G(L_T(\rho))
--   $$
--
--   for every normalized positive trace-class input $\rho$ on the full Fock space. The constructed maps are normal completely positive trace-preserving channels. Their Kraus sums converge in trace norm on every trace-class input, the Kraus matrices realize the indicated physical operators, and their output characteristic function is $\chi_{M(\rho)}(z)=\chi_\rho(\sqrt{\tau}z)e^{-\nu|z|^2/2}$ for every complex $z$. The coherent vectors and Weyl operators used in this identification are normalized and unitary as appropriate.
--
--   The factorization includes zero transmissivity, identity, and quantum-limited endpoints. For $TG=1$, its noise is $2(G-1)$; the printed example $2G-1$ is inconsistent with the source composition equation.
-- source:
--   Majorization theory approach to the Gaussian channel minimum entropy conjecture, arXiv:1111.1986v1, PDF p. 2, (4)–(5), Figure 1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P30

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- arXiv:1111.1986v1, PDF p.2, (4)-(5) and Figure 1. All phase-insensitive
channels equal vacuum loss followed by vacuum amplification, on all inputs.
The printed additive-noise example nu=2G-1 is replaced by nu=2(G-1), as forced
by the displayed noise composition law. Endpoints are included. -/
theorem channel_factorization (tau nu : ℝ) (htau : 0 ≤ tau) (hnu : |tau - 1| ≤ nu) :
    let G := (tau + nu + 1) / 2
    let T := 2 * tau / (tau + nu + 1)
    1 ≤ G ∧ 0 ≤ T ∧ T ≤ 1 ∧ tau = T * G ∧ nu = G * (1 - T) + (G - 1) ∧
    D.DisplacementRealized ∧ D.CoherentRealized ∧
    D.AttenuatorRealized (Real.sqrt T) ∧ D.AmplifierRealized (Real.sqrt G) ∧
    C.IsNormalFockChannel (phaseChannel tau nu) ∧ C.IsNormalFockChannel (loss T) ∧
    C.IsNormalFockChannel (C.amplifier G) ∧
    (∀ X : D.FockOperator, D.IsTraceClass X →
      D.TraceHasSum (fun j => D.krausTerm (D.attenuatorKraus (Real.sqrt T) j) X) (loss T X) ∧
      D.TraceHasSum (fun j => D.krausTerm (D.amplifierKraus (Real.sqrt G) j) X)
        (C.amplifier G X)) ∧
    (∀ X : D.FockOperator, D.IsDensity X →
      D.IsDensity (phaseChannel tau nu X) ∧ D.IsDensity (loss T X) ∧
      D.IsDensity (C.amplifier G X) ∧
      phaseChannel tau nu X = C.amplifier G (loss T X) ∧
      ∀ z : ℂ, D.characteristic (phaseChannel tau nu X) z =
        D.characteristic X ((Real.sqrt tau : ℂ) * z) *
          Complex.exp (-(nu * Complex.normSq z / 2 : ℝ))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P30

end
