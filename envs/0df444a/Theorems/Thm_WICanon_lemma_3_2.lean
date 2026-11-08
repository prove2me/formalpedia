-- Prove2me | Theorems.Thm_WICanon_lemma_3_2
-- name    : WICanon.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:08:04.1067+00:00
-- url     : https://prove2.me/theorems/e8b31269-21c7-4a6e-bb63-602e6a7471ba
-- title:
--   Lemma 3.2 — round collapse for constant-round deterministic-prover SWI
-- statement:
--   Assume a $k$-round honest-verifier deterministic-prover $\delta$-SWI public-coin interactive argument for $\mathcal R$ with $(1-\alpha)$-completeness and $\epsilon$-soundness error, prover-to-verifier communication $\ell_P\in\mathrm{poly}$ and total communication $\ell$, where $k$ is a constant and $\epsilon<1/64$. Then either infinitely-often auxiliary-input one-way functions exist, or there is a two-message (AM) honest-verifier deterministic-prover public-coin interactive argument for $\mathcal R$ with negligible soundness error that is
--
--   $$\bigl(\delta(n)\cdot\mathrm{poly}(\ell_P,\log n)^k\bigr)\text{-SWI},\qquad\bigl(1-\alpha\cdot\mathrm{poly}(\ell_P,\log n)^k\bigr)\text{-complete},$$
--
--   with communication $\ell\cdot\mathrm{poly}(\ell_P,\log n)^k$. If the argument is $\epsilon$-statistically sound, the result is statistically sound with negligible error.
--
--   **Formalization Note** The factor is $T=(\ell_P(n)+\lceil\log_2 n\rceil+2)^{ck}$ for a universal $c$ chosen before the protocol. Both soundness variants are clauses.
--
--   Differences from the source:
--   - reading: poly(ℓP, log n)^k → (ℓP(n) + ⌈log₂ n⌉ + 2)^(c·k) for a universal c chosen before the protocol; reason: the proof gives ℓ²_P,i·polylog(n) per step with exponents independent of the protocol, and Theorem 3.3 sets ε′ from T
--   - reading: a constant number k of rounds → 1 ≤ k; reason: a protocol with no rounds is run as one with an empty first round; with k = 0 the printed factor would be 1, which leaves no room for the repetition
--   - reading: ϵ < 1/64 → ϵ a function with ϵ(n) < 1/64 for all n; reason: the proof of Theorem 3.3 applies it to a function; a constant is an instance
--   - reading: for every x ∉ L and every non-uniform PPT prover: acceptance ≤ β(|x|) → each prover is bound from some length on, and it receives x; reason: the literal order lets the prover depend on x and collapses computational to statistical soundness
--   - reading: relation R → R with a polynomial witness bound; reason: the index a = (x, w0, w1) in {0,1}^m(n) and the PPT prover presuppose it
--   - encoding: states st_V,i, st_P,i and per-round coins → next-message functions of the history, one coin tape per party; reason: a state is computed from the coins and the messages; same protocols
--   - encoding: a possibly inefficient randomized prover → a deterministic reply function; reason: a randomized prover's acceptance probability is an average over its coins
--   - encoding: P̂ with coins → a non-uniform machine with one coin tape across rounds; reason: a prover keeps its tape; advice per length |x|
--   - reading: ρ_i = r_V,i, st_V,i = ∅ (public coin) → ρ_i an injective encoding of the block r_V,i, and the decision a function of x and the whole transcript; reason: printed with Out := V*(y, st_V,k, m_k) the decision would read m_k alone, against this lemma's own proof (p.28); the encoding keeps OR-repetition public coin, and the prover can apply it to recover ρ_i = r_V,i
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Lemma 3.2, p.17 (restated as Lemma 3.17, p.28)

import Mathlib
import Definitions.Def_OWFLocalDesc_Negligible
import Definitions.Def_WICanon_IsNPRelation
import Definitions.Def_WICanon_ProtocolProps
import Definitions.Def_WICanon_Soundness
import Definitions.Def_WICanon_WitnessIndist
import Definitions.Def_WICanon_AIOWF
import Definitions.Def_WICanon_Compilations

set_option autoImplicit false

namespace WICanon

open OWFLocalDesc

/-- **Lemma 3.2** (round collapse; restated as Lemma 3.17, p.28). Arnon, Mazor, Pass, Silbak, *Does
Witness Indistinguishability Require Cryptography?*, STOC 2027 submission manuscript (sha256 3f78ec3d…),
p.17. A `k`-round honest-verifier deterministic-prover `δ`-SWI public-coin argument for `R` with
`(1 − α)`-completeness and `ϵ`-soundness, `ϵ < 1/64`, `k` constant, gives: either infinitely-often AI-OWFs,
or a two-message honest-verifier deterministic-prover `δ·T`-SWI public-coin argument with negligible
soundness, `(1 − α·T)`-completeness and communication `ℓ·T`, for `T = poly(ℓP, log n)^k`; statistically
sound with negligible error if the argument is `ϵ` statistically sound.

**Formalization Note.** The exponent `c` is universal, chosen before the protocol, as the proof gives
(`m = ℓ²_{P,i}·polylog(n)` per step and `polylog(n)` repetition, pp.28–29), and as Theorem 3.3 needs: `ε′` is
set from `T`. `1 ≤ k`: a protocol with no rounds is run as one with an empty first round. -/
theorem lemma_3_2 : ∃ c : ℕ, ∀ (R : Relation) (qw : Polynomial ℕ) (_ : WitnessBound R qw) (k : ℕ)
    (_ : 1 ≤ k) (pv : Protocol) (_ : pv.IsEfficient) (_ : pv.rounds = fun _ => k)
    (_ : pv.IsPublicCoin) (_ : pv.IsDeterministicProver) (δ α εs : ℕ → ℝ)
    (_ : HonestSWI pv R δ) (_ : CompleteAt pv R α) (_ : ∀ n, εs n < 1 / 64) (LP : Polynomial ℕ)
    (L : ℕ → ℕ) (_ : pv.TotalProverBound R LP.eval) (_ : pv.TotalCommBound R L),
    (SoundCompAt pv R εs → IOAIOWFExist ∨ ∃ pvHat : Protocol,
      IsRoundCollapse pvHat R δ α L (collapseFactor c k LP.eval) ∧ SoundCompNegl pvHat R) ∧
    (SoundStatAt pv R εs → IOAIOWFExist ∨ ∃ pvHat : Protocol,
      IsRoundCollapse pvHat R δ α L (collapseFactor c k LP.eval) ∧
        ∃ β, Negligible β ∧ SoundStatAt pvHat R β) := by sorry

end WICanon
