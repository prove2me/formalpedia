-- Prove2me | Theorems.Thm_WICanon_theorem_2_11
-- name    : WICanon.theorem_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:07:06.993908+00:00
-- url     : https://prove2.me/theorems/fae06ace-124f-4369-a0e2-aa4490e06339
-- title:
--   Theorem 2.11 ([CHKT26]) — from private to public coin
-- statement:
--   Assume that infinitely-often auxiliary-input one-way functions do not exist. Let $(P,V)$ be a $\beta$-sound, $(1-\alpha)$-complete honest-verifier $\epsilon$-WI argument for $\mathcal R$ with a constant number $k$ of rounds. Then for any $q\in\mathrm{poly}$ there is a $(\beta+1/q)$-sound, $(1-\alpha-1/q)$-complete, $k$-round honest-verifier $(\epsilon+1/q)$-WI public-coin argument for $\mathcal R$. If the original protocol is statistically sound, then the resulting protocol is $(\beta+1/q)$-statistically sound. The prover-to-verifier communication stays the same.
--
--   It lets the rest of the proof assume a public-coin protocol.
--
--   **Formalization Note** One protocol carries both soundness clauses: statistical soundness implies computational soundness with the same $\beta$, so a proof is an instance of the hypothesis.
--
--   Differences from the source:
--   - reading: for every x, w0, w1 and every non-uniform PPT D: advantage < δ(|x|) → each D is bound from some length on; reason: the literal order lets D depend on x, and a table in the finite control collapses WI to SWI at every x; the reading is a weaker hypothesis
--   - encoding: non-uniform D with advice z_n on inputs of length n → advice and 1^n indexed by n = |x|; reason: |x| is the security parameter of the notion; the view determines no input length in general
--   - reading: for every x ∉ L and every non-uniform PPT prover: acceptance ≤ β(|x|) → each prover is bound from some length on, and it receives x; reason: the literal order lets the prover depend on x and collapses computational to statistical soundness
--   - reading: relation R → R with a polynomial witness bound; reason: the index a = (x, w0, w1) in {0,1}^m(n) and the PPT prover presuppose it
--   - encoding: states st_V,i, st_P,i and per-round coins → next-message functions of the history, one coin tape per party; reason: a state is computed from the coins and the messages; same protocols
--   - encoding: prover coins polynomial in |x| + |w| → a coin count depending on |x|; reason: witnesses are polynomially bounded and a machine may ignore coins
--   - encoding: a possibly inefficient randomized prover → a deterministic reply function; reason: a randomized prover's acceptance probability is an average over its coins
--   - encoding: P̂ with coins → a non-uniform machine with one coin tape across rounds; reason: a prover keeps its tape; advice per length |x|
--   - reading: ρ_i = r_V,i, st_V,i = ∅ (public coin) → ρ_i an injective encoding of the block r_V,i, and the decision a function of x and the whole transcript; reason: printed with Out := V*(y, st_V,k, m_k) the decision would read m_k alone, against the proof of Lemma 3.2 (p.28); the encoding keeps OR-repetition public coin, and the prover can apply it to recover ρ_i = r_V,i
--   - encoding: 1/q → 1/(q(n) + 1); reason: meaningful at q(n) = 0; covers every polynomial q ≥ 1
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Theorem 2.11, p.14

import Mathlib
import Definitions.Def_WICanon_PolyBounds
import Definitions.Def_WICanon_IsNPRelation
import Definitions.Def_WICanon_ProtocolProps
import Definitions.Def_WICanon_Soundness
import Definitions.Def_WICanon_WitnessIndist
import Definitions.Def_WICanon_AIOWF

set_option autoImplicit false

namespace WICanon

/-- **Theorem 2.11** ([CHKT26]; private to public coin). Arnon, Mazor, Pass, Silbak, *Does Witness
Indistinguishability Require Cryptography?*, STOC 2027 submission manuscript (sha256 3f78ec3d…), p.14.
Assume infinitely-often AI-OWFs do not exist. A `β`-sound, `(1 − α)`-complete honest-verifier `ε`-WI argument
for `R` with a constant number `k` of rounds gives, for any `q ∈ poly`, a `(β + 1/q)`-sound,
`(1 − α − 1/q)`-complete, `k`-round honest-verifier `(ε + 1/q)`-WI public-coin argument, `(β + 1/q)`-statistically
sound if the original is statistically sound, with the same prover-to-verifier communication.

**Formalization Note.** One protocol carries both soundness clauses. Statistical soundness implies
computational soundness with the same `β`, so a proof is an instance of the hypothesis. -/
theorem theorem_2_11 (hno : ¬ IOAIOWFExist) (R : Relation) (qw : Polynomial ℕ)
    (hw : WitnessBound R qw) (k : ℕ) (pv : Protocol) (hpv : pv.IsEfficient)
    (hk : pv.rounds = fun _ => k) (α β ε : ℕ → ℝ) (hc : CompleteAt pv R α)
    (hs : SoundCompAt pv R β) (hWI : HonestWI pv R ε) (q : Polynomial ℕ) :
    ∃ pv' : Protocol, pv'.IsEfficient ∧ pv'.IsPublicCoin ∧ pv'.rounds = (fun _ => k) ∧
      CompleteAt pv' R (fun n => α n + oneOver q n) ∧
      SoundCompAt pv' R (fun n => β n + oneOver q n) ∧
      HonestWI pv' R (fun n => ε n + oneOver q n) ∧
      (SoundStatAt pv R β → SoundStatAt pv' R (fun n => β n + oneOver q n)) ∧
      ∀ LP : ℕ → ℕ, pv.TotalProverBound R LP → pv'.TotalProverBound R LP := by sorry

end WICanon
