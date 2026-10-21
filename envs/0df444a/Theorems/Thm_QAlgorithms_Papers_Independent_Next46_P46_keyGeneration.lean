-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P46_keyGeneration
-- name    : QAlgorithms.Papers.Independent.Next46.P46.keyGeneration
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:00:31.963013+00:00
-- url     : https://prove2.me/theorems/742b5b64-b768-4b9c-b13b-1aed17a18d8b
-- title:
--   Unassisted secret-key generation at coherent information
-- statement:
--   Fix an isometric dilation $U:A'\to BE$ of a finite-dimensional channel, giving Eve all of $E$, and a unit state $|\psi'\rangle^{AA'}$ initially entirely on Alice's side. Let $R=H(B)-H(AB)$ in the one-use output source.
--
--   For every $\varepsilon,\delta>0$ and all sufficiently large positive $n$, there are an integer $M>0$, normalized block inputs $\rho_m$ on $(A')^{\otimes n}$, and a single Bob POVM with outcomes $1,\ldots,M$. Alice chooses $m$ uniformly and sends $\rho_m$ through $U^{\otimes n}$. Writing $K_A,K_B$ for her message and Bob's outcome, the resulting joint state obeys, for some normalized $\theta^{E^n}$,
--
--   $$
--   \frac{\log_2M}{n}\ge R-\delta,\qquad
--   \left\|\omega^{K_AK_BE^n}-\frac1M\sum_{m=1}^M|mm\rangle\!\langle mm|\otimes\theta^{E^n}\right\|_1\le\varepsilon.
--   $$
--
--   The inputs and decoder are selected before the random message, and no side communication is used. This states the operational private-coding conclusion in the source's trace-distance sense.
-- source:
--   Relating quantum privacy and quantum coherence: an operational approach, arXiv:quant-ph/0307053v1, PDF p. 3, Key generation (3.)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P46

open QAlgorithms

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.decEq Classical.propDecidable

-- The repair request explicitly authorizes imports from the pinned accepted papers.

open QAlgorithms.Papers.Independent.Information100.P21 (Vec Op)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open QAlgorithms.Papers.Independent.Frontier30.P12
  (coherentInfo quantumMutualInfo mutualAE marginalAE triCopies EntProtocol RectangularKrausData)

open QAlgorithms.Papers.Independent.Dependency50.P19 (channelSource)

open QAlgorithms.Papers.Independent.Dependency50.P48 (IsDilation)

/-- arXiv:quant-ph/0307053v1, PDF pp.1--3, scenario 3: private generation at I_c.
The code and its single Bob POVM are chosen before the uniform message.
The common Eve state is arbitrary; the disputed literal PA subset claim is not assumed. -/
theorem keyGeneration {A P B E : Type} [Fintype A] [Fintype P] [Fintype B] [Fintype E]
    [Nonempty A] [Nonempty P] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) P ℂ) (hU : IsDilation U)
    (psi : Vec (A × P)) (hpsi : IsState psi) :
    DynamicPrivateAchievable U
      (coherentInfo (marginalAB (pureDensity (channelSource U psi)))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P46

end
