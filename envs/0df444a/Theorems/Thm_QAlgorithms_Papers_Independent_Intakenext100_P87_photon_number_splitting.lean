-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P87_photon_number_splitting
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P87.photon_number_splitting
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:22:09.336422+00:00
-- url     : https://prove2.me/theorems/b5765d4e-96d6-4ac0-993c-320418f70606
-- title:
--   Supplementary Note 1: complete BB84 break at zero bit error with enough loss
-- statement:
--   Consider identically polarized BB84 pulses with photon-number probabilities $p_n\ge0$, $\sum_np_n=1$, independent of the bit and basis. Bob has a basis-independent signal-click response $0\le d(j)\le1$. Define $A=\sum_{n\ge2}p_nd(n-1)$. If the honest signal rate satisfies $0\le q\le A$, a polarization-independent thinning probability $t\in[0,1]$ exists for the following attack: block pulses with fewer than two photons, retain one photon from each forwarded pulse, and send the rest through a superior channel. After the basis announcement, matched-basis measurement gives
--
--   $$tA=q,\qquad\Pr[B=b,E=e,\mathrm{click}\mid\mathrm{bit}=a,\mathrm{basis}=u]=q\,\mathbf1_{b=e=a}.$$
--
--   Thus the signal rate is matched, sifted bit errors are zero, and Eve learns every signal bit. Extraction is explicitly a split of pre-existing tensor factors. Arbitrary countable number distributions, including Poisson pulses, are covered; no photon cutoff or cloning map is assumed.
-- source:
--   Unconditional Security Of Quantum Key Distribution Over Arbitrarily Long Distances, arXiv:quant-ph/9803006v5, PDF p. 19, Supplementary Note 1: complete BB84 break at zero bit error with enough loss

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P87

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P87

open scoped Matrix ComplexConjugate

open QAlgorithms.Measurements

/-- PDF pp.14,19, Supplementary Note 1: whenever multiphoton-only forwarding can
match the honest signal rate q, one polarization-independent thinning attack matches
that rate, causes zero sifted bit errors, and lets Eve recover every sifted bit.
The pulse statistics are arbitrary normalized nonnegative sequences, including Poisson.
The exact extraction factorization explicitly uses pre-existing photons. -/
theorem photon_number_splitting (p d : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (hnorm : HasSum p 1) (hd : ∀ n, 0 ≤ d n ∧ d n ≤ 1)
    (q : ℝ) (hq : 0 ≤ q) (hfeasible : q ≤ pnsForwardRate p d) :
    (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ t * pnsForwardRate p d = q ∧
      ∀ basis bit bob eve : Bool,
        pnsKeyLaw p d t basis bit bob eve = if bob = bit ∧ eve = bit then q else 0) ∧
    (∀ (n : ℕ) (basis bit : Bool),
      extractedPulse n basis bit = tensorVec (bb84SignalKet basis bit) (photonPulse n basis bit)) ∧
    (∀ mu : ℝ, 0 ≤ mu → (∀ n, 0 ≤ poissonMass mu n) ∧ HasSum (poissonMass mu) 1) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P87

end
