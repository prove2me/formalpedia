-- Prove2me | Theorems.Thm_SeedRecyclingDL_Codes_theorem_C_7
-- name    : SeedRecyclingDL.Codes.theorem_C_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:27.241526+00:00
-- url     : https://prove2.me/theorems/bc027d1f-f9f6-4cba-ae68-286e57d95ca9
-- title:
--   Theorem C.7 — Encoding and decoding complexity
-- statement:
--   Fix $t\ge1$ and the Section 4 field and competitor parameters. An operational tag service encodes tags and tests/inverts its image in time $\tau_A(n)$ after precomputation. Uniform finite programs realize encoder (5) and Procedure B.2 with
--   $$\begin{aligned}
--   \text{encoding}&:O_t(n^{2t+2}\log_2^2n)+O(\tau_A),\
--   \text{payload}&:O_t(n^{t+1}\log_2n)+O_t(n^t)\tau_A,\
--   \text{full message}&:O_t(n^{2t+2}\log_2^2n)+O_t(n^t)\tau_A.
--   \end{aligned}$$
--   All query terms remain explicit. Decoders halt on every finite input. Program choices precede lengths; constants multiplying query counts are uniform over the tag service, and the encoder's one-call coefficient is absolute. This exposes the costs needed to instantiate either suffix variant.
--
--   Differences from the source:
--   - encoding: binary strings and one-based positions → lists of Fin 2 with length predicates and current-word zero-based positions; reason: the order-preserving representation includes empty intermediate words and every unrestricted DL script
--   - encoding: the binary polynomial-basis field of order 2^b → a published finite-field Presentation with characteristic parameter 2, degree b, and its coefficient coordinates; reason: the quotient isomorphism and reconstruction certify the same field; coordinate order is constant coefficient first, and integer value is most significant bit first
--   - encoding: asymptotic deterministic bit complexity → finite programs with actual charged RAM executions and uniform positive constants before lengths and inputs; reason: the fixed instruction semantics generates costs; a function with an assigned runtime is not accepted
--   - reading: bit operations on a RAM without a prescribed tape layout → helper routines use length and packed-value natural cells, while main and generic decoders receive raw bit streams; reason: each cell read and output is charged by bit length; raw decoder streams permit bounded inspection of arbitrarily long invalid inputs
--   - generalization: the Section 4 greedy or bootstrapped tag code → any operational tag service with 1 <= N <= n/2 and the same separation property; reason: both source services are instances and all three query-dependent bounds are retained
--   - encoding: a tag code available for all sufficiently large n → the service is assumed valid from an arbitrary threshold n1 of its own, and the bounds hold for n at least max(n0, n1), with the constants and n0 chosen before the service; reason: the source's tag codes exist only for large n, and the theorem's constants do not depend on where they start
-- source:
--   Quan D. Bui, Manabu Hagiwara, Shuche Wang, Van Khu Vu, STOC 2027 submission #1449 (October 2026), Theorem C.7, printed p. 20 (PDF p. 22); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1449.pdf

import Definitions.Def_SeedRecyclingDL_Codes_Interfaces

set_option autoImplicit false

namespace SeedRecyclingDL.Codes

theorem theorem_C_7 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ t : ℕ, 1 ≤ t → ∃ (Ct : ℝ) (n₀ : ℕ), 0 < Ct ∧
      ∀ (data : ℕ → FieldData) (S : TagService) (n₁ : ℕ),
        (∀ n : ℕ, max n₀ n₁ ≤ n → (data n).presentation.p = 2 ∧
          (data n).presentation.k = fieldWidth t n ∧ 1 ≤ S.suffix n ∧
          S.suffix n ≤ n / 2 ∧ OperationalTag data S t n) →
        ∃ encoder decoder payload : Program, ∀ n : ℕ, max n₀ n₁ ≤ n →
          ∀ saved : MachineState, SetupState (serviceCells data S n) saved →
            (∀ mu : Word, mu.length = n - S.suffix n + 2 * fieldWidth t n - 2 →
              ResumedExecutes encoder n saved (mu.map Fin.val)
                (some ((serviceEncoder data S t n mu).map Fin.val))
                (onlineBound Ct t n + C₀ * S.time n)) ∧
            (∀ y : Word,
              ResumedExecutes payload n saved (y.map Fin.val)
                ((servicePayload data S t n y).map (List.map Fin.val))
                (payloadBound Ct t n + Ct * (n : ℝ) ^ t * S.time n)) ∧
            (∀ y : Word,
              ResumedExecutes decoder n saved (y.map Fin.val)
                ((serviceDecoder data S t n y).map (List.map Fin.val))
                (onlineBound Ct t n + Ct * (n : ℝ) ^ t * S.time n)) := by sorry

end SeedRecyclingDL.Codes
