-- Prove2me | Theorems.Thm_RegevRecon_proposition_2
-- name    : RegevRecon.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:08:22.616149+00:00
-- url     : https://prove2.me/theorems/86ab6e2d-ca9b-44b7-a2d4-4eaad3c1683a
-- title:
--   Proposition 2 — global decoding from tree decoding [MPRP26]
-- statement:
--   Let $B$ be drawn from the ensemble of Definition 2. At a fixed $\beta\ge0$, let $\mu$ be the channel vector for the common target set $S$. If the recurrence of §5 satisfies $E[P_{\mathrm{err}}(v^{(\ell)})]\to0$, then a decoder runs in polynomial time and decodes a uniformly chosen codeword of $C^\perp=\ker B^T$ with ensemble-average error probability tending to zero as $m$ increases.
--
--   Concretely, a machine writes from $B$ and the digits of $\beta$, within $C(n+1)^K$ steps, a circuit over $\{H,T,\mathrm{CNOT}\}$ with at most $C(n+1)^K$ gates and wires, whose block error, averaged over graph and coefficients, is at most $\delta_n\to0$. This lifts tree decoding to the entire codeword.
--
--   Differences from the source:
--   - reading: "for a suitable ℓ = Θ(log log m), the BPQM decoder with erasure recovery of [MPRP26, Theorem 30]" → the existence of a polynomial-time decoder circuit family, without naming BPQM or ℓ; reason: that algorithm is specified only in [MPRP26], so it cannot be pinned from this source; the hypothesis ties the statement to the BPQM recursion
--   - reading: "polynomial-time" (the paper names no model) → a deterministic multi-stack Turing machine (Turing.TM2ComputableAux Bool Bool) writes a circuit over the finite gate set {H, T, CNOT} within C(n+1)^K steps, with at most C(n+1)^K gates and wires; reason: the paper names no machine or gate set; a fixed finite gate set is the strong reading, since gates with real parameters could carry the reals of the instance for free
--   - reading: every fixed real β, with no statement of how the algorithm knows β → the input word holds the binary digits of ⌊2ⁿβ⌋, and the machine may depend on β; reason: with no digits on the input the clause is false for uncomputable β, since the circuit would be a computable function of the instance; restricting to computable β would be a special case
--   - reading: a decoding circuit on the received system → wires laid out as received (m·b), estimate (m·b), then work, with b = ⌈log₂ p⌉; reason: the paper fixes no layout; p.16 describes these registers
--   - encoding: laws of random vectors, =d → finitely supported Law; =d is equality of masses at every whole vector; reason: all these vectors take finitely many values; same instances
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), Proposition 2, p.15; (40), p.16

import Mathlib
import Definitions.Def_RegevRecon_qLaw
import Definitions.Def_RegevRecon_DecoderCircuit

namespace RegevRecon

open Filter Topology

/-- **Proposition 2 (Global decoding from tree decoding [MPRP26])**. Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), p.15: at any fixed `β ≥ 0`, if the recurrence
of §5 satisfies `E[P_err(v^(ℓ))] → 0`, then the decoder runs in polynomial time and decodes a uniformly chosen
codeword of `C^⊥ = ker Bᵀ` with ensemble-average error probability tending to zero.

**Formalization Note** A machine `M` writes, from `B` and the digits of `β` and within `C (n+1)^K` steps, a circuit over
`{H, T, CNOT}` with wires for the received word, the estimate and work. The statement asserts the existence of such a
decoder and does not name BPQM's internals: the algorithm of [MPRP26, Theorem 30] is not specified in this source. The
block error is averaged over graph and coefficients only; it has no offsets, as "the shifts τ_j are implemented by
phase gates in Regev's reduction" (p.16). -/
theorem proposition_2 {p : ℕ} [Fact p.Prime] {k D : ℕ} (hk : 3 ≤ k) (hkD : k < D)
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hS' : S ≠ Finset.univ)
    (Λ : PMF (Fin D → (ZMod p)ˣ)) (hΛ : Exchangeable Λ)
    (β : ℝ) (hβ : 0 ≤ β)
    (h : Tendsto (fun ℓ => (vLaw k D S Λ β ℓ).expect pErr) atTop (𝓝 0)) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C K : ℕ) (δ : ℕ → ℝ), Tendsto δ atTop (𝓝 0) ∧
      ∀ n : ℕ, k ∣ n * D →
        ∃ circ : Matrix (Fin (n * D / k)) (Fin n) (ZMod p) → Circ,
          (∀ Bbar ∈ biregular k D (n * D / k) n, ∀ c : Fin n → Fin D → (ZMod p)ˣ,
            (∀ j, Λ (c j) ≠ 0) →
              HMBinPacking.OutputsWithin M (encMatrix (fillMatrix Bbar c) ++ encBeta n β)
                  (encCirc (circ (fillMatrix Bbar c))) (C * (n + 1) ^ K) ∧
                (circ (fillMatrix Bbar c)).gates.length ≤ C * (n + 1) ^ K ∧
                (circ (fillMatrix Bbar c)).wires ≤ C * (n + 1) ^ K ∧
                2 * (n * D / k) * regBits p ≤ (circ (fillMatrix Bbar c)).wires) ∧
          graphAverage k (n * D / k) n Λ (fun B => circBlockError B S β (circ B)) ≤ δ n := by sorry

end RegevRecon
