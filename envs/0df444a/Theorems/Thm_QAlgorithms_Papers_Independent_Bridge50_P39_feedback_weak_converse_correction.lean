-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P39_feedback_weak_converse_correction
-- name    : QAlgorithms.Papers.Independent.Bridge50.P39.feedback_weak_converse_correction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:51:36.177397+00:00
-- url     : https://prove2.me/theorems/94b92a3e-7a7e-4b32-b990-eca6e31d8805
-- title:
--   A finite real weak-converse correction with the source iterated limits
-- statement:
--   Fix a quantum channel $\mathcal N:A\to B$ between positive, finite-dimensional complex Hilbert spaces. There exist real-valued functions $g_{\mathcal N}(n,\varepsilon)$ and $\ell_{\mathcal N}(\varepsilon)$, chosen uniformly over codes, such that
--
--   $$
--   \forall\,0\le\varepsilon<1,\quad
--   \lim_{n\to\infty}g_{\mathcal N}(n,\varepsilon)=\ell_{\mathcal N}(\varepsilon),\qquad
--   \lim_{\varepsilon\downarrow0}\ell_{\mathcal N}(\varepsilon)=0.
--   $$
--
--   For every valid protocol $P$ using the same memoryless channel $n\ge1$ times with $L\ge1$ uniform messages, every advertised rate $0\le R\le\log_2 L/n$, and actual average decoding error $\varepsilon=1-p_{\mathrm{succ}}(P)$ satisfying $0\le\varepsilon<1$,
--
--   $$
--   R\le\chi(\mathcal N)+g_{\mathcal N}(n,\varepsilon).
--   $$
--
--   This holds when $\mathcal N$ is entanglement-breaking without encoding restrictions, and for arbitrary $\mathcal N$ when every actual pre-use conditional state, conditioned on message and complete classical transcript, is fully separable across retained Alice memory, current input and Bob memory. Protocols have arbitrary finite local quantum memories, noiseless classical feedback including $X_0$, no initially shared entanglement or message-dependent Bob seed, and a final $L$-outcome decoding POVM. The success probability is computed by executing the fixed maps and averaging the correct-message Born probabilities. The quantity $\chi(\mathcal N)$ optimizes the ordinary output Holevo information over finite mixed-state ensembles, with base-two entropy.
--
--   This is the finite weak-converse statement reproduced from Bowen and Nagarajan. The length limit is taken first; no explicit correction coefficient is asserted.
--
--   **Formalization Note** The printed theorem leaves the error endpoint implicit. The coding assertion uses $\varepsilon<1$: at $\varepsilon=1$ an always-wrong decoder with arbitrarily many messages rules out a finite correction uniform over codes.
-- source:
--   Strong converse exponents for the feedback-assisted classical capacity of entanglement-breaking channels, arXiv:1506.02228v4, PDF p. 16, Theorem 7, (B.1)-(B.2)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P39

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (relativeD tensorAction)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB ordinaryClassicalCapacity)

open QAlgorithms.Papers.Independent.Information100.P08 (channelHolevo)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Support50.P19
  (channelInformation informationRadius expTwo)

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- PDF pp.16-18, Theorem 7 (reproducing BN05), (B.1)-(B.2).
The printed domain omits epsilon<1; this reliable-communication domain is required:
at epsilon=1, arbitrary message counts preclude a finite uniform real correction.
The inner n-limit precedes the outer epsilon-down-to-zero limit. One correction
function is selected before ALL codes for the fixed channel. -/
theorem feedback_weak_converse_correction [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) :
    ∃ g : ℕ → ℝ → ℝ, ∃ limitInLength : ℝ → ℝ,
      (∀ e : ℝ, 0 ≤ e → e < 1 →
        Tendsto (fun n : ℕ => g n e) atTop (nhds (limitInLength e))) ∧
      Tendsto limitInLength (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      ∀ n L : ℕ, ∀ P : FeedbackCode A B n L,
        P.Valid → (IsEB N ∨ P.SeparableInputs N) →
        ∀ R : ℝ, 0 ≤ R → R ≤ uniformMessageRate n L →
        0 ≤ P.error N → P.error N < 1 →
        R ≤ channelHolevo N + g n (P.error N) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P39

end
