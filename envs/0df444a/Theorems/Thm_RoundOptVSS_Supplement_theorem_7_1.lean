-- Prove2me | Theorems.Thm_RoundOptVSS_Supplement_theorem_7_1
-- name    : RoundOptVSS.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:13:49.486585+00:00
-- url     : https://prove2.me/theorems/6934cbe6-24be-4f6d-943c-d4763e53d167
-- title:
--   Theorem 7.1 — the protocol of §7.2 is a (3, 1)-round key-uniform WSS with key length $m_{\mathrm{WS}}$, perfect privacy, polynomial complexity and error $\varepsilon_{\mathrm{WSS}}$
-- statement:
--   Let $\mathbb F\subseteq\mathbb E$ be finite fields and fix the public constants of §5.1 and §7.2 (packing nodes $\beta$, the point $\alpha_0$, party points $a_i$) satisfying the standing assumptions. Let $t<n/2$. Against a static rushing adversary corrupting at most $t$ parties, the protocol of §7.2 with the packed IC of §5.1 is
--
--   1. of broadcast-then-decode type (Definition 6.1) with three sharing rounds, one reconstruction round and key length $m_{\mathrm{WS}}=6(n-1)(n-2)$;
--   2. a key-uniform WSS (Definitions 4.1 and 6.2) with perfect sharing privacy and error
--   $$\varepsilon_{\mathrm{WSS}}=Mn\Big(\frac1{q-1}+\frac{\delta}{|\mathcal A|}\Big),\qquad q=|\mathbb F|,\quad \delta=h+t-1,\quad M=(n-1)(t+1)+3(n-1)(n-2);$$
--   3. of polynomial communication and computation: there are one polynomial $p$ and one program for each honest map, independent of the fields and of the parameters, such that every honest map runs within $p(n+h+\text{input size})$ field and integer operations on every input, and every honest state and message, the message cap and the number of coins per round are of size at most $p(n+h)$.
--
--   This is the key-uniform WSS that the compiler of §8 turns into a VSS (Theorem 8.1 combines it with Theorem 8.7).
--
--   **Formalization Note** The scheme is `wssScheme cfg`, its layout `wssLayout cfg`; the cost model is `RoundOptVSS.Supplement.Cost`. All clauses hold for every $n,t$ with $2t<n$, every dealer index and every $h$, at every parameter set satisfying the standing assumptions.
--
--   Differences from the source:
--
--   - encoding: the protocol of Section 7.2, instantiated with the IC of Section 5.1 → wssScheme cfg: Protocols 4–7 transcribed in the base execution model (state = the party's view; tagged-item messages, first matching item read, missing or malformed value = ⊥, missing flag = 1; the decoder of Protocol 7 is the base mission's Dec); reason: a rule-by-rule transcription of pp.17 and 20–23
--   - encoding: uniform B, pads, F, G with val(F) = x, d ← 𝔽^×, α_w ← 𝒜 → coins drawn per domain (𝔼, 𝔽^×, 𝒜) by fixed enumerations; B from independent coefficients b_kl = b_lk with b_00 = s; F = c + Interp_β(x − val(c)) with c uniform; every party draws the same coin pattern; reason: each is exactly the uniform law the page prescribes
--   - encoding: standing assumptions: h ≥ 1, distinct β with β_1 = 0 if h = 1, α_0 ∈ 𝒜 ≠ ∅, distinct nonzero party points a_i ∈ 𝔽 → CfgAdm cfg, a hypothesis of every security, communication and computation clause, for arbitrary finite fields 𝔽 ⊆ 𝔼 and constants cfg; reason: the protocol is defined under these assumptions (pp.17 and 20)
--   - generalization: party indices are distinct nonzero elements a_i of 𝔽 (all n parties) → distinct and nonzero required only for the row holders i ≠ D; reason: the dealer's point is never evaluated (rows, overlaps and the interpolation of Protocol 7 use row holders' points only), so the statement specializes to the page's whenever all n points are distinct and nonzero
--   - encoding: three sharing rounds, one reconstruction round → fixed by the type Protocol of the base model; reason: the model has exactly rounds 0, 1, 2 and 3
--   - encoding: key length mWS, broadcast-then-decode form, κ_w fixed after round one → IsBTDOn and (wssScheme cfg).ℓ P = mWS n, with κ_w in a fixed public order of the S and Q labels; reason: Definition 6.1 and the verification-vector paragraph of p.21
--   - reading: polynomial communication and computation → ∃ p and one program per honest map, before the fields and the parameters: time ≤ p(n + h + input size) on every input in the cost model RoundOptVSS.Supplement.Cost; coin count, cap, honest states and honest messages of size ≤ p(n + h); reason: the paper counts field elements and field operations (proof of Theorem 7.1, Lemma 7.8); κ is not used by the scheme
--   - encoding: field operations of 𝔽 and 𝔼 → an algebraic RAM over 𝔼 with 𝔽 held as its image, and a unit-cost test "lies in 𝔽"; reason: recognising a valid key (point in 𝒜 ⊆ 𝔽) reads coordinates in any representation of 𝔼 over 𝔽
--   - encoding: messages of arbitrary length → public message cap 1000(n + h + 2)^4, above every honest message; reason: the base model reads an over-cap message as missing
--   - encoding: error at most εWSS → probabilities ≥ 1 − εWSS in ℝ≥0∞ with εWSS = M·n·((q − 1)⁻¹ + δ/|𝒜|); reason: same numbers
-- source:
--   Liu-Zhang, Masserova, Round-Optimal Statistical Verifiable Secret Sharing with Polynomial Complexity, manuscript (2026; STOC 2027 submission, sha256 3a45d95d…), Theorem 7.1 and (7) (p.24), with §5.1 (p.17), §7.2 (pp.20–23), Definitions 4.1, 6.1, 6.2 (pp.15, 18–19)

import Mathlib
import Definitions.Def_RoundOptVSS_Model
import Definitions.Def_RoundOptVSS_Supplement_Cost
import Definitions.Def_RoundOptVSS_Supplement_KeyUniform
import Definitions.Def_RoundOptVSS_Supplement_WSSProtocol

open scoped ENNReal

namespace RoundOptVSS

namespace Supplement

/-- **Theorem 7.1** (Key-uniform WSS), p.24 of Liu-Zhang, Masserova, *Round-Optimal Statistical
Verifiable Secret Sharing with Polynomial Complexity*, manuscript (STOC 2027 submission, sha256
3a45d95d…): for `t < n/2`, against a static rushing adversary, the protocol of §7.2 with the IC of
§5.1 is a key-uniform WSS (Definitions 4.1 and 6.2) with three sharing rounds, one reconstruction
round, key length `mWS`, perfect sharing privacy, polynomial communication and computation, and
error (7) `εWSS = Mn(1/(q − 1) + δ/|A|)`, `q = |𝔽|`, `δ = h + t − 1`.

**Formalization Note.** The three sharing rounds and one reconstruction round are fixed by the type
`Protocol`. The scheme is `wssScheme cfg` for arbitrary finite fields `𝔽 ⊆ 𝔼` and constants `cfg`
(packing nodes, `α₀`, party points); every security clause is for all `n, t` with `2t < n`, every
dealer index and `h`, every corrupt set with `|C| ≤ t` and every adversary, at every parameter set
satisfying the standing assumptions `CfgAdm cfg`. "Polynomial communication and computation" is in
the field-operation cost model `RoundOptVSS.Supplement.Cost`: one polynomial `p` and one program per
honest map, chosen before the fields and the parameters, with time `p(n + h + input size)` and
honest state and message sizes `p(n + h)`. -/
theorem theorem_7_1 :
    ∃ (p : Polynomial ℕ) (codes : Codes),
      ∀ (𝔽 𝔼 : Type) [Field 𝔽] [Fintype 𝔽] [Field 𝔼] [Fintype 𝔼] [Algebra 𝔽 𝔼]
        (cfg : (P : Params) → WSSCfg 𝔽 P),
        IsBTDOn (CfgAdm cfg) (wssScheme (𝔼 := 𝔼) cfg) ∧
        (∀ P : Params, (wssScheme (𝔼 := 𝔼) cfg).ℓ P = mWS P.n) ∧
        IsKeyUniformWSSOn (CfgAdm cfg) (wssScheme (𝔼 := 𝔼) cfg) (epsWSS cfg) ∧
        Computation 𝔽 (CfgAdm cfg) (wssLayout (𝔼 := 𝔼) cfg) (wssScheme (𝔼 := 𝔼) cfg).prot
          (fun P => P.n + P.h) p codes ∧
        Communication (CfgAdm cfg) (wssLayout (𝔼 := 𝔼) cfg) (wssScheme (𝔼 := 𝔼) cfg).prot
          (fun P => P.n + P.h) p := by sorry

end Supplement

end RoundOptVSS
