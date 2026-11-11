-- Prove2me | Theorems.Thm_QFairEx_lemma_4_10
-- name    : QFairEx.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:26:32.832945+00:00
-- url     : https://prove2.me/theorems/41a8ba8c-912c-4f9c-8fd5-718fcfd664c1
-- title:
--   Lemma 4.10 — stopping across an inactive round leaves $p_p$ unchanged
-- statement:
--   For every valid protocol, all vectors $e_{p,a}$ defining the encodings, and every round $r\in\{1,\dots,T\}$:
--   $$p_0(r)=p_0(r-1)\ \text{ if $r$ is odd},\qquad p_1(r)=p_1(r-1)\ \text{ if $r$ is even}.$$
--
--   In an odd round the stopped party $P_1$ has no outgoing slot, so stopping it before or after that round is the same to $P_0$ and the trusted party; symmetrically in even rounds.
--
--   Differences from the source:
--   - generalization: a protocol in the communication model of Definition 4.1 (exchange parties doing quantum computation, a classical trusted party) → every valid Protocol: arbitrary completely positive instruments on finite registers, classical memories and messages over arbitrary types (including a classical part of the message between the exchange parties), an auxiliary initial cq-state that may correlate all three processes; reason: the class only grows, and every protocol of the paper is one of these
--   - encoding: register and message types may change from round to round → one register type and one alphabet per process and slot for all rounds; reason: round-dependent finite registers embed isometrically into one of maximal dimension and round-dependent alphabets into their sum type, so every such protocol is simulated with identical output law
--   - encoding: after its cut the fail-stop party keeps receiving and processing but sends nothing → the stopped party's registers are traced out and its memory summed at the cut; abort is supplied in its scheduled slots and messages addressed to it are discarded; reason: its later processing acts only on its own registers and cannot change the joint state of the honest party and the trusted party (the paper's argument in the proofs of Lemmas 4.10 and 4.12)
--   - encoding: the decision and output are produced by the honest party's processing in round T → a separate decision instrument (branches acc, rej) applied after round T; reason: composing it into the round-T processing gives the same outputs
--   - generalization: the encodings use orthonormal e_{p,0}, e_{p,1} ∈ S_p, in the setting of perfect security → arbitrary vectors e_{p,a}, no security hypothesis; reason: the lemma's proof uses neither; the paper's encodings are a special case
--   - encoding: pure states |ψ⟩ → density matrices |ψ⟩⟨ψ| (vectors ι → ℂ with the standard inner product); reason: global phase is not observable; same instances
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), Lemma 4.10, p.23

import Mathlib
import Definitions.Def_QFairEx_Protocol
import Definitions.Def_QFairEx_Protocol_IsValid
import Definitions.Def_QFairEx_Protocol_pAcc

namespace QFairEx

/-- **Lemma 4.10 (stopping across an inactive round).** Chung, Lee, Raizes, Thyagarajan,
*Quantum Fair Exchange*, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883…),
Lemma 4.10, p.23: "For every r ∈ {1, . . . , T}, p0(r) = p0(r − 1) if r is odd, p1(r) =
p1(r − 1) if r is even."

For every valid protocol and all encodings `e0`, `e1` (no security assumption), and every
round `1 ≤ r ≤ T`: `p₀(r) = p₀(r − 1)` if `r` is odd, and `p₁(r) = p₁(r − 1)` if `r` is even. -/
theorem lemma_4_10 {ι0 ι1 : Type} [Fintype ι0] [Fintype ι1] [DecidableEq ι0] [DecidableEq ι1]
    (e0 : Fin 2 → ι0 → ℂ) (e1 : Fin 2 → ι1 → ℂ)
    (P : Protocol ι0 ι1) (hP : P.IsValid) (r : ℕ) (hr1 : 1 ≤ r) (hrT : r ≤ P.T) :
    (Odd r → P.pAcc e0 e1 0 r = P.pAcc e0 e1 0 (r - 1)) ∧
      (Even r → P.pAcc e0 e1 1 r = P.pAcc e0 e1 1 (r - 1)) := by sorry

end QFairEx
