-- Prove2me | Theorems.Thm_QFairEx_ralt_marginal
-- name    : QFairEx.ralt_marginal
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:27:33.087395+00:00
-- url     : https://prove2.me/theorems/41fe0867-f72b-4f8f-8237-03b68f7c6ed6
-- title:
--   Proof of Lemma 4.12 — each party's marginal in $R_{\mathrm{alt}}(t)$ is its output in $\mathrm{Stop}(p,t)$
-- statement:
--   For every valid protocol and every cut $t\le T$:
--
--   1. for every input operator $X$ on $\iota_0\times\iota_1$, in the joint experiment of Algorithm 4.11 (steps 1–3), $P_0$'s output conditioned on its own decision, with $P_1$'s output traced out and $P_1$'s decision summed, equals its conditional output in Stop$(0,t)$, and likewise $P_1$'s equals its conditional output in Stop$(1,t)$;
--   2. averaging over the sixteen challenge pairs, for all encodings,
--   $$\Pr_{R_{\mathrm{alt}}(t)}[f_p=\mathrm{acc}]=p_p(t),\qquad p\in\{0,1\}.$$
--
--   The copy of the classical trusted state and the disjointness of the two continuations make each continuation reproduce the corresponding stopping execution.
--
--   Differences from the source:
--   - generalization: a protocol in the communication model of Definition 4.1 (exchange parties doing quantum computation, a classical trusted party) → every valid Protocol: arbitrary completely positive instruments on finite registers, classical memories and messages over arbitrary types (including a classical part of the message between the exchange parties), an auxiliary initial cq-state that may correlate all three processes; reason: the class only grows, and every protocol of the paper is one of these
--   - encoding: register and message types may change from round to round → one register type and one alphabet per process and slot for all rounds; reason: round-dependent finite registers embed isometrically into one of maximal dimension and round-dependent alphabets into their sum type, so every such protocol is simulated with identical output law
--   - encoding: after its cut the fail-stop party keeps receiving and processing but sends nothing → the stopped party's registers are traced out and its memory summed at the cut; abort is supplied in its scheduled slots and messages addressed to it are discarded; reason: its later processing acts only on its own registers and cannot change the joint state of the honest party and the trusted party (the paper's argument in the proofs of Lemmas 4.10 and 4.12)
--   - encoding: the decision and output are produced by the honest party's processing in round T → a separate decision instrument (branches acc, rej) applied after round T; reason: composing it into the round-T processing gives the same outputs
--   - reading: the honest party accepts and outputs a state supported on S_{1−b}, or rejects and outputs a state supported on S_b → the acc branch outputs on Ver_{1−b}'s register ι_{1−b}, the rej branch on Ver_b's register ι_b; reason: Definition 4.3 compares the accepted output with S_{1−b} and the rejected one with S_b
--   - encoding: pure states |ψ⟩ → density matrices |ψ⟩⟨ψ| (vectors ι → ℂ with the standard inner product); reason: global phase is not observable; same instances
--   - generalization: for every fixed pair of encoded challenge inputs → for every input operator X on ι0 × ι1 (and, for the averaged identity, every choice of vectors e_{p,a}); reason: the identity is linear in the input; the challenge inputs are a special case
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), proof of Lemma 4.12, p.25

import Mathlib
import Definitions.Def_QFairEx_kronMap
import Definitions.Def_QFairEx_SupportedOn
import Definitions.Def_QFairEx_bb84
import Definitions.Def_QFairEx_encVec
import Definitions.Def_QFairEx_Protocol
import Definitions.Def_QFairEx_Protocol_IsValid
import Definitions.Def_QFairEx_Protocol_stopAcc0
import Definitions.Def_QFairEx_Protocol_pAcc
import Definitions.Def_QFairEx_Protocol_ralt

namespace QFairEx

open Matrix

/-- **Marginals of the joint stopping experiment (proof of Lemma 4.12).** Chung, Lee, Raizes,
Thyagarajan, *Quantum Fair Exchange*, STOC 2027 submission (manuscript of 2026-11-02, sha256
0099b883…), proof of Lemma 4.12, p.25: "Hence, before decoding and guessing, the decision and
quantum-output marginal of Pp in Ralt(t) agrees with its output in Stop(p, t) for every fixed
pair of challenge inputs. In particular, after averaging over those inputs,
Pr_{Ralt(t)}[fp = acc] = pp(t), p ∈ {0, 1}."

For a valid protocol, a cut `t ≤ T` and every input operator `X` on `ι0 × ι1`: in the joint
experiment of Algorithm 4.11 (steps 1–3), P₀'s output conditioned on its own decision, with
P₁'s output traced out and P₁'s decision summed, equals its conditional output in Stop(0, t);
likewise for P₁ and Stop(1, t). After averaging over the 16 encoded challenge pairs,
`Pr_{R_alt(t)}[f_p = acc] = p_p(t)` for any encodings `e0`, `e1`. -/
theorem ralt_marginal {ι0 ι1 : Type} [Fintype ι0] [Fintype ι1] [DecidableEq ι0] [DecidableEq ι1]
    (P : Protocol ι0 ι1) (hP : P.IsValid) (t : ℕ) (ht : t ≤ P.T) :
    (∀ X : Matrix (ι0 × ι1) (ι0 × ι1) ℂ,
      ptraceRight (P.jointAccAcc X t) + ptraceRight (P.jointAccRej X t) = P.stopAcc0 X t ∧
      ptraceRight (P.jointRejAcc X t) + ptraceRight (P.jointRejRej X t) = P.stopRej0 X t ∧
      ptraceLeft (P.jointAccAcc X t) + ptraceLeft (P.jointRejAcc X t) = P.stopAcc1 X t ∧
      ptraceLeft (P.jointAccRej X t) + ptraceLeft (P.jointRejRej X t) = P.stopRej1 X t) ∧
    ∀ (e0 : Fin 2 → ι0 → ℂ) (e1 : Fin 2 → ι1 → ℂ),
      (1 / 16 : ℝ) * ∑ x : Fin 2 → Bool, ∑ θ : Fin 2 → Bool,
          ((P.jointAccAcc (encodeInput e0 e1 (pureDensity (bb84Vec θ x))) t).trace +
            (P.jointAccRej (encodeInput e0 e1 (pureDensity (bb84Vec θ x))) t).trace).re =
        P.pAcc e0 e1 0 t ∧
      (1 / 16 : ℝ) * ∑ x : Fin 2 → Bool, ∑ θ : Fin 2 → Bool,
          ((P.jointAccAcc (encodeInput e0 e1 (pureDensity (bb84Vec θ x))) t).trace +
            (P.jointRejAcc (encodeInput e0 e1 (pureDensity (bb84Vec θ x))) t).trace).re =
        P.pAcc e0 e1 1 t := by sorry

end QFairEx
