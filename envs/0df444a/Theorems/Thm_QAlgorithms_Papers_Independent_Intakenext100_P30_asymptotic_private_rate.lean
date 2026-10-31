-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P30_asymptotic_private_rate
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P30.asymptotic_private_rate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:54:59.737674+00:00
-- url     : https://prove2.me/theorems/60a7a904-3e39-4e73-8d0a-a7b4225f59c9
-- title:
--   Regularized private rate with messagewise secrecy
-- statement:
--   Fix receiver and eavesdropper cq marginals $\Theta_Y$ and $\Theta_Z$ on the same input alphabet. The operational iterated limit and the regularized information limit exist and agree:
--
--   $$
--   R_{\rm prv}(\Theta)
--   =\lim_{\varepsilon\downarrow0}\lim_{n\to\infty}\frac{C_{\rm prv}^{\varepsilon}(\Theta^{\otimes n})}{n}
--   =\lim_{\ell\to\infty}\frac1\ell\sup_{P_T,T\to X^\ell}
--   \bigl[H(T|Z^{\otimes\ell})-H(T|Y^{\otimes\ell})\bigr].
--   $$
--
--   The optimization includes every finite auxiliary $T$, every law on it, and every stochastic map to the full input string. The operational capacity uses messagewise reliability and secrecy relative to one normalized message-independent reference. This is the source's regularized private transmission formula.
--
--   All alphabets are finite and nonempty, and output Hilbert spaces are finite dimensional and nonzero. A classical–quantum channel assigns a positive semidefinite, trace-one matrix to each input. Encoders may use private randomness; decoders are normalized POVMs. Codes are fixed independently of the message, with no supplied shared key or entanglement. Logarithms and entropies are in bits.
-- source:
--   Noisy channel coding via privacy amplification and information reconciliation, arXiv:1012.4814v2, PDF p. 5, §IV (17): regularized private rate

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakenext100.P30

variable {X Y Z M U V A B C : Type*}

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z] [Fintype M] [DecidableEq M]

variable [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C]

attribute [local instance] Classical.propDecidable

/-- Section IV, PDF p.5, (15), (17): regularized private rate. The optimization
has no supplied auxiliary-dimension bound. The two limits and their common value
are conclusions; neither Lemma 5 nor a derived entropy bound is assumed. -/
theorem asymptotic_private_rate [Nonempty X] [Nonempty Y] [Nonempty Z]
    (thetaY : X → Matrix Y Y ℂ) (thetaZ : X → Matrix Z Z ℂ)
    (hY : RRIsCq thetaY) (hZ : RRIsCq thetaZ) :
    ∃ rate : ℝ, RRPrivateRate thetaY thetaZ rate ∧
      Tendsto (fun n : ℕ => rrPerUse (n + 1)
        (rrPrivateInformation (rrChannelPower thetaY (n + 1))
          (rrChannelPower thetaZ (n + 1)))) atTop (nhds (rate : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P30

end
