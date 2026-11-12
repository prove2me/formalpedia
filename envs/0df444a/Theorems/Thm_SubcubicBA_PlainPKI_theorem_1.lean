-- Prove2me | Theorems.Thm_SubcubicBA_PlainPKI_theorem_1
-- name    : SubcubicBA.PlainPKI.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:43:16.737872+00:00
-- url     : https://prove2.me/theorems/63444812-243f-4757-888c-d509f93b298b
-- title:
--   Theorem 1 — deterministic Byzantine agreement for t < n/2 with O(n) rounds and O(κ^((√13−1)/2) n^((√13+1)/2)) bits
-- statement:
--   Work in the synchronous model with $n$ parties, authenticated channels and a plain public-key infrastructure, where signatures and hashes have $\kappa$ bits, and in the regime $\kappa=\Omega(\log n)$, $\kappa=\mathrm{polylog}(n)$ of §4. For all constants $c_1,K,C>0$ there are a deterministic protocol family $\Pi$ and a constant $A>0$ such that for all $n\ge1$, $t$ with $2t<n$, and $\kappa$ with
--   $$c_1\log_2 n\le\kappa\le K(\log_2 n)^C,$$
--   for every set $F$ of at most $t$ byzantine parties, every binary input vector and every execution against a rushing, computationally unbounded adversary:
--   1. **Termination:** every honest party outputs a bit within $\lfloor An\rfloor$ rounds;
--   2. **Validity:** if all honest inputs equal $c$, every honest output is $c$;
--   3. **Agreement:** any two honest outputs are equal;
--   4. **Silence:** honest parties send nothing from round $\lfloor An\rfloor$ on;
--   5. **Bits:** the total size of all messages sent by honest parties over the whole execution is at most
--   $$A\,\kappa^{(\sqrt{13}-1)/2}\,n^{(\sqrt{13}+1)/2}\approx A\,\kappa^{1.303}n^{2.303}.$$
--
--   This is the first subcubic deterministic byzantine agreement protocol at optimal resiliency $t<n/2$ that uses only ordinary signatures; all earlier plain-PKI protocols at this resiliency have cubic communication.
--
--   **Formalization Note** The paper writes $O(\cdot)$; the statement asserts a constant $A$ depending only on the κ-regime constants $c_1,K,C$ (proof of Theorem 9, p. 32), chosen before $n$, $t$, $\kappa$, $F$, the inputs and the adversary. Bits are counted over all rounds, and silence after the round bound rules out moving traffic past the window.
--
--   Differences from the source:
--   - encoding: R_BA(n) = O(n) and B_BA(n) = O(κ^{(√13−1)/2} n^{(√13+1)/2}) → one constant A, depending only on c₁, K, C and chosen before n, t, κ, F, the inputs and the adversary, bounding the decision round by ⌊A·n⌋ and the total honest bits by A·κ^{(√13−1)/2}·n^{(√13+1)/2}; reason: the explicit form of the O(·) as in the proof of Theorem 9 (p. 32)
--   - reading: κ = Ω(log n) and κ = polylog(n) (§4) → for all c₁, K, C > 0: c₁·log₂ n ≤ κ ≤ K·(log₂ n)^C; reason: the standing assumptions, quantified as in the proof of Theorem 9 (paper.md reading 2)
--   - encoding: round complexity and bit complexity of a protocol → termination by round ⌊A·n⌋, silence of honest parties from that round on, and the bound on the total size of honest messages over all rounds (every partial sum); reason: pins the complexity measures; excludes moving traffic past the round bound
--   - encoding: binary agreement, v_in ∈ {0, 1} (Definition 2) → inputs nat 0 / nat 1, outputs a bit, any session number, no auxiliary knowledge; reason: same instances
--   - reading: computationally unforgeable κ-bit signatures and a collision-resistant κ-bit hash (§4, p. 8) → idealized symbolic tokens: injective constructors sig p m, hash m; Dolev–Yao adversary; honest parties see tokens only through blinded shapes, equality tests and signature verification (with unbounded local computation they can recognise a token whose content they could construct themselves, but never obtain a signature they have not received); reason: every proof in the paper uses unforgeability and collision resistance as absolute facts (pp. 12, 16, 30) and no reduction appears (paper.md reading 1)
--   - generalization: a static adversary; rushing is not specified → a static rushing adversary: its round-r messages may depend on the honest round-r messages sent to corrupted parties; reason: a stronger adversary; every execution against a non-rushing adversary is one of these
--   - generalization: byzantine parties cannot forge signatures or invert the hash → the adversary may also open signature and hash tokens it holds (it still cannot create an honest party's signature); reason: a stronger adversary; the source's adversary is a special case
--   - encoding: messages of a given bit size; signatures and hashes of κ bits → symbolic terms of bit size: 2-bit tag per data node, a self-delimiting code for numbers, exactly κ bits per token; reason: the sizes of §4; constant per-node overheads do not change any instance's asymptotics
--   - encoding: instance tags on messages and signatures (§13) → every signature is domain-separated by the session number of its protocol instance; sub-instances get child sessions; reason: the §13 tags; replay across instances is excluded exactly as §13 intends
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), Theorem 1, p. 3 (restated as Final Result, p. 36)

import Mathlib
import Definitions.Def_SubcubicBA_PlainPKI_Model

namespace SubcubicBA.PlainPKI

/-- Theorem 1 (p. 3; restated p. 36). -/
theorem theorem_1 (c₁ K C : ℝ) (hc₁ : 0 < c₁) (hK : 0 < K) (hC : 0 < C) :
    ∃ (P : Protocol) (A : ℝ), 0 < A ∧
      ∀ (n t κ sess : ℕ), 1 ≤ n → 2 * t < n →
        c₁ * Real.logb 2 n ≤ (κ : ℝ) → (κ : ℝ) ≤ K * Real.logb 2 n ^ C →
        ∀ (b : Fin n → Bool) (F : Finset (Fin n)) (tr : Trace n), F.card ≤ t →
          IsRun P (baSetup sess t κ b F) ∅ tr →
            (∀ j : Fin n, j ∉ F → ∃ r ≤ ⌊A * n⌋₊, ∃ c : Bool,
                OutputsAt P (baSetup sess t κ b F) tr j r (Term.bit c)) ∧
            (∀ c : Bool, (∀ j : Fin n, j ∉ F → b j = c) → ∀ j : Fin n, j ∉ F → ∀ o : Term,
                Outputs P (baSetup sess t κ b F) tr j o → o = Term.bit c) ∧
            (∀ j k : Fin n, j ∉ F → k ∉ F → ∀ o o' : Term,
                Outputs P (baSetup sess t κ b F) tr j o →
                Outputs P (baSetup sess t κ b F) tr k o' → o = o') ∧
            SilentFrom (baSetup sess t κ b F) tr ⌊A * n⌋₊ ∧
            ∀ R : ℕ, (honestBitsUpTo (baSetup sess t κ b F) tr R : ℝ) ≤
              A * (κ : ℝ) ^ ((Real.sqrt 13 - 1) / 2) * (n : ℝ) ^ ((Real.sqrt 13 + 1) / 2) := by sorry

end SubcubicBA.PlainPKI
