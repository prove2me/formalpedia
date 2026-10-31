-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P30_asymptotic_public_rate
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P30.asymptotic_public_rate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:54:15.186532+00:00
-- url     : https://prove2.me/theorems/3a267100-f4fe-4b53-ac73-c062b4096d9c
-- title:
--   Regularized public rate for independent uses of a fixed cq channel
-- statement:
--   Fix the cq input alphabet and receiver channel $\Theta$. The operational iterated limit exists, as does the regularized information limit, and they agree:
--
--   $$
--   R_{\rm pub}(\Theta)
--   =\lim_{\varepsilon\downarrow0}\lim_{n\to\infty}\frac{C_{\rm pub}^{\varepsilon}(\Theta^{\otimes n})}{n}
--   =\lim_{\ell\to\infty}\frac1\ell\sup_{P_{X^\ell}}\bigl[H(X^\ell)-H(X^\ell|Y^{\otimes\ell})\bigr].
--   $$
--
--   Each input law may correlate the entire classical string; each code may use an arbitrary stochastic encoder and normalized decoder. The independent channel uses, not the codes or input laws, factor. This is the public classical communication formula for the fixed cq channel.
--
--   All alphabets are finite and nonempty, and output Hilbert spaces are finite dimensional and nonzero. A classical–quantum channel assigns a positive semidefinite, trace-one matrix to each input. Encoders may use private randomness; decoders are normalized POVMs. Codes are fixed independently of the message, with no supplied shared key or entanglement. Logarithms and entropies are in bits.
-- source:
--   Noisy channel coding via privacy amplification and information reconciliation, arXiv:1012.4814v2, PDF p. 5, §IV (16): regularized public rate

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

/-- Section IV, PDF p.5, (15)–(16): existence of the operational iterated limit
and its regularized public information formula on the fixed cq alphabet. -/
theorem asymptotic_public_rate [Nonempty X] [Nonempty Y]
    (theta : X → Matrix Y Y ℂ) (hTheta : RRIsCq theta) :
    ∃ rate : ℝ, RRPublicRate theta rate ∧
      Tendsto (fun n : ℕ => rrPerUse (n + 1)
        (rrPublicInformation (rrChannelPower theta (n + 1)))) atTop (nhds (rate : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P30

end
