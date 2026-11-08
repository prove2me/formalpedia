-- Prove2me | Theorems.Thm_WICanon_claim_2_12
-- name    : WICanon.claim_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:06:33.995988+00:00
-- url     : https://prove2.me/theorems/406e27ef-2c89-4a47-8041-e4dd014584cb
-- title:
--   Claim 2.12 — OR-parallel repetition
-- statement:
--   Let $(P,V)$ be a $\delta$-SWI interactive protocol with $(1-\alpha)$-completeness and $\beta$-soundness. Then the $t$-fold independent parallel repetition with OR accepting condition is a $t\delta$-SWI interactive protocol with $(1-\alpha^t)$-completeness and $t\beta$-soundness.
--
--   It amplifies completeness at the cost of a factor $t$ in the other two errors, and is the last step of the proof of Theorem 3.3.
--
--   **Formalization Note** The statement also records what the proof of Theorem 3.3 uses (p.17): the repetition preserves the number of rounds, public coin, and the determinism of the prover. $t$ may depend on $|x|$. The efficient version of the repetition and its computational soundness are for an efficient base protocol and a $t$ that a machine computes.
--
--   Differences from the source:
--   - reading: t-fold repetition, β-soundness → t a function of |x|; soundness in both variants, the computational one for an efficient base protocol and polynomially bounded computable t; reason: the printed claim does not name the variant; a cheating prover for one copy has to simulate the others
--   - reading: for every x ∉ L and every non-uniform PPT prover: acceptance ≤ β(|x|) → each prover is bound from some length on, and it receives x; reason: the literal order lets the prover depend on x and collapses computational to statistical soundness
--   - encoding: states st_V,i, st_P,i and per-round coins → next-message functions of the history, one coin tape per party; reason: a state is computed from the coins and the messages; same protocols
--   - encoding: a possibly inefficient randomized prover → a deterministic reply function; reason: a randomized prover's acceptance probability is an average over its coins
--   - encoding: P̂ with coins → a non-uniform machine with one coin tape across rounds; reason: a prover keeps its tape; advice per length |x|
--   - reading: ρ_i = r_V,i, st_V,i = ∅ (public coin) → ρ_i an injective encoding of the block r_V,i, and the decision a function of x and the whole transcript; reason: printed with Out := V*(y, st_V,k, m_k) the decision would read m_k alone, against the proof of Lemma 3.2 (p.28); the encoding keeps OR-repetition public coin, and the prover can apply it to recover ρ_i = r_V,i
--   - generalization: the printed three bounds → also preservation of the number of rounds, of public coin and of a deterministic prover; reason: the proof of Theorem 3.3 uses these (p.17); dropping the extra conjuncts gives the printed claim
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Claim 2.12, p.14

import Mathlib
import Definitions.Def_WICanon_PolyBounds
import Definitions.Def_WICanon_IsNPRelation
import Definitions.Def_WICanon_ProtocolProps
import Definitions.Def_WICanon_Soundness
import Definitions.Def_WICanon_WitnessIndist
import Definitions.Def_WICanon_OrRepeat

set_option autoImplicit false

namespace WICanon

/-- **Claim 2.12** (OR-parallel repetition). Arnon, Mazor, Pass, Silbak, *Does Witness Indistinguishability
Require Cryptography?*, STOC 2027 submission manuscript (sha256 3f78ec3d…), p.14. The `t`-fold independent
parallel repetition with OR accepting condition of a `δ`-SWI protocol with `(1 − α)`-completeness and
`β`-soundness is `tδ`-SWI with `(1 − α^t)`-completeness and `tβ`-soundness.

**Formalization Note.** Also: rounds, public coin and determinism of the prover are preserved (used on
p.17). Both soundness notions are covered; the computational one needs an efficient base protocol and
a `t` a machine can compute, since a cheating prover for one copy simulates the others. -/
theorem claim_2_12 (R : Relation) (pv : Protocol) (δ α β : ℕ → ℝ) (t : ℕ → ℕ)
    (hSWI : HonestSWI pv R δ) (hc : CompleteAt pv R α) :
    HonestSWI (orRepeat pv t) R (fun n => (t n : ℝ) * δ n) ∧
    CompleteAt (orRepeat pv t) R (fun n => α n ^ t n) ∧
    (SoundStatAt pv R β → SoundStatAt (orRepeat pv t) R (fun n => (t n : ℝ) * β n)) ∧
    (pv.IsEfficient → IsPolyLen t → (orRepeat pv t).IsEfficient ∧
      (SoundCompAt pv R β → SoundCompAt (orRepeat pv t) R (fun n => (t n : ℝ) * β n))) ∧
    (orRepeat pv t).rounds = pv.rounds ∧
    (pv.IsPublicCoin → (orRepeat pv t).IsPublicCoin) ∧
    (pv.IsDeterministicProver → (orRepeat pv t).IsDeterministicProver) := by sorry

end WICanon
