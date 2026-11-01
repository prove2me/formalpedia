-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P65_gkp_largeEnergyMoments
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P65.gkp_largeEnergyMoments
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:34:29.842697+00:00
-- url     : https://prove2.me/theorems/65286d21-f1e3-415d-bad9-c33296985761
-- title:
--   Large-energy moments of individually normalized smeared GKP states
-- statement:
--   Use the Gaussian-displacement-smearing choice (7.7c) with parameter $0<\Delta\le1$. Its position wavefunction is proportional to
--
--   $$w_{\mu,\Delta}(x)=\sum_{n\in\mathbb Z}\exp\!\left[-\frac{(x-q_n)^2}{2\Delta^2}-\frac{\Delta^2(x+q_n)^2}{8}\right],\qquad q_n=\sqrt\pi(2n+\mu).$$
--
--   Normalize each logical wavefunction separately in $L^2(\mathbb R)$ and take its coefficients in the normalized Hermite (Fock) basis. The coefficients have unit squared norm and finite moments of every nonnegative integer order. Write $m_k(\Delta)$ for the half-sum of the two kth photon-number moments and $\bar n(\Delta)=m_1(\Delta)$. Then, for every fixed integer $k\ge0$,
--
--   $$\frac{\bar n(\Delta)}{1/(2\Delta^2)-1/2}\to1,\qquad \frac{m_k(\Delta)}{k!\,\bar n(\Delta)^k}\to1\quad(\Delta\downarrow0).$$
--
--   The mixture is the literal half-sum of two rank-one densities. Their finite-$\Delta$ orthogonality and an exact finite-energy geometric law are not assumed.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, PDF p. 18, §VII (7.9)–(7.10): large-energy GKP moments

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.18 (7.9)--(7.10): ratio asymptotics for moments of (7.7c), using
individually normalized vectors and their literal half-sum, not an orthogonal projector. -/
theorem gkp_largeEnergyMoments :
    (∀ d ∈ Set.Ioc (0 : ℝ) 1, ∀ mu : Fin 2,
      fockDomain (gkpFock d mu) ∧ fockNormSq (gkpFock d mu) = 1 ∧
      ∀ k : ℕ, fockMomentDomain (gkpFock d mu) k) ∧
    Tendsto (fun d : ℝ => codeMoment (gkpFock d) 1 / (1 / (2 * d ^ 2) - 1 / 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) ∧
    (∀ k : ℕ, Tendsto (fun d : ℝ => codeMoment (gkpFock d) k /
      ((Nat.factorial k : ℝ) * codeMoment (gkpFock d) 1 ^ k))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P65

end
