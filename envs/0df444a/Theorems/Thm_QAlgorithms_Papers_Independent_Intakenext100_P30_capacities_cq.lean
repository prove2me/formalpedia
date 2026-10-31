-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P30_capacities_cq
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P30.capacities_cq
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:57:36.226146+00:00
-- url     : https://prove2.me/theorems/4fe310cc-9b2f-497c-a54d-8a683a10b602
-- title:
--   One-shot public and private cq capacity bounds
-- statement:
--   Let $\Theta_Y$ and $\Theta_Z$ be the receiver and eavesdropper cq marginals on a common classical input alphabet $X$. For $\varepsilon>0$, let $C_{\rm pub}^{\varepsilon}$ be the supremum of $\log_2|M|$ over codes whose decoding error is at most $\varepsilon$ for every message. Let $C_{\rm prv}^{\varepsilon}$ additionally require, for every message, half the trace norm distance of Eve's output to one fixed normalized reference to be at most $\varepsilon$. Then
--
--   $$
--   \begin{aligned}
--   C_{\rm pub}^{\varepsilon}(\Theta)&\ge\sup_{P_X}\bigl[H_{\min}^{\varepsilon/8}(X)-H_{\max}^{\varepsilon/8}(X|Y)\bigr]-4\log_2(1/\varepsilon)-16,\\
--   C_{\rm pub}^{\varepsilon}(\Theta)&\le\sup_{P_X}\bigl[H_{\min}(X)-H_{\max}^{\sqrt{2\varepsilon}}(X|Y)\bigr],\\
--   C_{\rm prv}^{8\varepsilon}(\Theta)&\ge\sup_{P_T,T\to X}\bigl[H_{\min}^{\varepsilon/8}(T|Z)-H_{\max}^{\varepsilon/8}(T|Y)\bigr]-4\log_2(1/\varepsilon)-16,\\
--   C_{\rm prv}^{\varepsilon}(\Theta)&\le\sup_{P_T,T\to X}\bigl[H_{\min}^{\sqrt{2\varepsilon}}(T|Z)-H_{\max}^{\sqrt{2\varepsilon}}(T|Y)\bigr].
--   \end{aligned}
--   $$
--
--   The private optimizations range over every finite nonempty auxiliary alphabet $T$, every law $P_T$, and every stochastic map $T\to X$, using the resulting Markov chain $T\to X\to(Y,Z)$. Suprema are extended-real, without an assumption of attainment. These are the four finite-resource bounds used to characterize public and private transmission.
--
--   All alphabets are finite and nonempty, and output Hilbert spaces are finite dimensional and nonzero. A classical–quantum channel assigns a positive semidefinite, trace-one matrix to each input. Encoders may use private randomness; decoders are normalized POVMs. Codes are fixed independently of the message, with no supplied shared key or entanglement. Logarithms and entropies are in bits.
--
--   For a normalized cq state, smoothing ranges over positive subnormalized matrices at purified distance at most the indicated radius. Smooth min-entropy is an extended supremum and smooth max-entropy an extended infimum; at the zero operator their unsmoothed values are respectively $+\infty$ and $-\infty$.
-- source:
--   Noisy channel coding via privacy amplification and information reconciliation, arXiv:1012.4814v2, PDF p. 2, Theorem 1: Capacities of Classical-Quantum Channels (seed pinned to (4)–(7))

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

/-- Theorem 1, PDF p.2, (4)–(7). All epsilon > 0 are retained using extended
suprema. For radius >= 1, Hmin = +infinity and Hmax = -infinity; the differences
used here contain no infinity-minus-infinity. Capacity is +infinity for error >= 1.
The input alphabet and the two cq marginals are fixed. -/
theorem capacities_cq [Nonempty X] [Nonempty Y] [Nonempty Z]
    (thetaY : X → Matrix Y Y ℂ) (thetaZ : X → Matrix Z Z ℂ)
    (hY : RRIsCq thetaY) (hZ : RRIsCq thetaZ) (epsilon : ℝ) (he : 0 < epsilon) :
    rrPublicDirectInfo thetaY (epsilon / 8) -
        ((4 * Real.logb 2 (1 / epsilon) + 16 : ℝ) : EReal) ≤ rrPublicCapacity thetaY epsilon ∧
    rrPublicCapacity thetaY epsilon ≤ rrPublicConverseInfo thetaY (Real.sqrt (2 * epsilon)) ∧
    rrPrivateInfo thetaY thetaZ (epsilon / 8) -
        ((4 * Real.logb 2 (1 / epsilon) + 16 : ℝ) : EReal) ≤
      rrPrivateCapacity thetaY thetaZ (8 * epsilon) ∧
    rrPrivateCapacity thetaY thetaZ epsilon ≤ rrPrivateInfo thetaY thetaZ (Real.sqrt (2 * epsilon)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P30

end
