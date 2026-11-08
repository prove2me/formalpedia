-- Prove2me | Theorems.Thm_WICanon_theorem_3_1
-- name    : WICanon.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:08:13.406506+00:00
-- url     : https://prove2.me/theorems/5d6e5f0f-c601-48c1-91f7-87892fea9ccf
-- title:
--   Theorem 3.1 — WI gives an ioAI-OWF or a deterministic-prover SWI protocol
-- statement:
--   Let $(P,V)$ be an honest-verifier $\varepsilon$-WI argument [resp., proof] for $\mathcal R$ with $(1-\alpha)$-completeness and $\beta$-soundness, $\ell$ a polynomial bound on the transcript length, $\ell_P$ a polynomial bound on the communication of $P$ in each round, and $k$ the number of rounds. Then at least one of the following holds.
--
--   1. The family $f_a(i,b,r_P,r_V)=\langle P(x,w_b;r_P),V(x;r_V)\rangle_{\le i}$, for $a=(x,w_0,w_1)$ with both pairs in $\mathcal R_n$, is an infinitely-often distributional auxiliary-input one-way function.
--   2. For every polynomial $q$ there is a protocol $(\hat P,\hat V)$ with $\hat P$ a deterministic polynomial-time algorithm, which is an honest-verifier $\gamma$-statistical WI argument [resp., proof] for $\mathcal R$ with $(1-\alpha-1/q)$-completeness, $\beta$-soundness and
--
--   $$\gamma\le k\cdot\ell_P\cdot3\varepsilon+1/q.$$
--
--   Moreover $\hat P$ has the per-round bound of $P$, and if $(P,V)$ is public-coin then so is $(\hat P,\hat V)$.
--
--   This is the paper's first main transformation.
--
--   **Formalization Note** The conclusion also records that the number of rounds is preserved, which the construction gives and Lemma 3.2 needs. The bound is the printed one with $\\ell_P$ any per-round upper bound, for messages of fixed or of variable length; the printed proof treats fixed lengths ("a message of the same format and length", p.23).
--
--   Differences from the source:
--   - reading: for every x, w0, w1 and every non-uniform PPT D: advantage < δ(|x|) → each D is bound from some length on; reason: the literal order lets D depend on x, and a table in the finite control collapses WI to SWI at every x; the reading is a weaker hypothesis
--   - encoding: non-uniform D with advice z_n on inputs of length n → advice and 1^n indexed by n = |x|; reason: |x| is the security parameter of the notion; the view determines no input length in general
--   - reading: for every x ∉ L and every non-uniform PPT prover: acceptance ≤ β(|x|) → each prover is bound from some length on, and it receives x; reason: the literal order lets the prover depend on x and collapses computational to statistical soundness
--   - reading: relation R → R with a polynomial witness bound; reason: the index a = (x, w0, w1) in {0,1}^m(n) and the PPT prover presuppose it
--   - reading: ε a distinguishing advantage → ε(n) ≥ 0; reason: with WI read asymptotically, a negative ε at a short length would be unconstrained and make the SWI bound unsatisfiable there; at long lengths a negative ε only occurs where no witness exists
--   - encoding: states st_V,i, st_P,i and per-round coins → next-message functions of the history, one coin tape per party; reason: a state is computed from the coins and the messages; same protocols
--   - encoding: prover coins polynomial in |x| + |w| → a coin count depending on |x|; reason: witnesses are polynomially bounded and a machine may ignore coins
--   - reading: f_a on a = (x, w0, w1) with both pairs in R_n, existence of a in {0,1}^m(n) → an index set of valid a, padded with empty components of the tuple code; reason: Theorem 3.1 and Lemma 3.10 define f_a only there
--   - reading: codomain {0,1}^m(n) in Definition 2.6 → free codomain; reason: Theorem 3.1's family outputs prefixes of varying length and Theorem 3.7's has codomain {0,1}^ℓ(n)
--   - reading: index i uniform in [ℓ] → i = min(val(s) + 1, L) for s uniform in {0,1}^⌈log₂ L⌉; reason: the input of a family is a uniform bit string; each value keeps probability at least 1/(2L)
--   - encoding: first i bits of the transcript → first i bits of the transcript written with the tuple code; reason: a fixed injective encoding, needed for messages of varying length
--   - encoding: A(a, y) → A(1^n, a, y); reason: |a| ≥ 2n for this family, so 1^n adds no power
--   - encoding: a possibly inefficient randomized prover → a deterministic reply function; reason: a randomized prover's acceptance probability is an average over its coins
--   - encoding: P̂ with coins → a non-uniform machine with one coin tape across rounds; reason: a prover keeps its tape; advice per length |x|
--   - encoding: 1/q → 1/(q(n) + 1); reason: meaningful at q(n) = 0; covers every polynomial q ≥ 1
--   - reading: ρ_i = r_V,i, st_V,i = ∅ (public coin) → ρ_i an injective encoding of the block r_V,i, and the decision a function of x and the whole transcript; reason: printed with Out := V*(y, st_V,k, m_k) the decision would read m_k alone, against the proof of Lemma 3.2 (p.28); the encoding keeps OR-repetition public coin, and the prover can apply it to recover ρ_i = r_V,i
--   - generalization: alternative 2 as printed → also pvHat.rounds = pv.rounds; reason: the construction keeps the k rounds of (P, V) (p.23) and Lemma 3.2 needs it; dropping the conjunct gives the printed alternative
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Theorem 3.1, pp.16–17

import Mathlib
import Definitions.Def_WICanon_IsNPRelation
import Definitions.Def_WICanon_ProtocolProps
import Definitions.Def_WICanon_Soundness
import Definitions.Def_WICanon_WitnessIndist
import Definitions.Def_WICanon_DistAIOWF
import Definitions.Def_WICanon_TranscriptFamily
import Definitions.Def_WICanon_Compilations

set_option autoImplicit false

namespace WICanon

/-- **Theorem 3.1** (Arnon, Mazor, Pass, Silbak, *Does Witness Indistinguishability Require
Cryptography?*, STOC 2027 submission manuscript, sha256 3f78ec3d…, pp.16–17). For an honest-verifier
`ε`-WI argument [resp., proof] `(P, V)` with `(1 − α)`-completeness and `β`-soundness, at least one holds:
(1) the transcript family is an infinitely-often distributional AI-OWF; (2) for every polynomial `q` there
is a deterministic-prover honest-verifier `γ`-SWI argument [resp., proof] with `(1 − α − 1/q)`-completeness
and `β`-soundness, `γ ≤ k·ℓP·3ε + 1/q`; `P̂` has the same per-round bound and public coin is preserved.

**Formalization Note.** The two conjuncts are the argument and proof variants. `ε ≥ 0` excludes only the
degenerate negative advantage at short lengths, where `HonestWI` says nothing. The bound is the printed one
with `ℓP` any per-round upper bound, for messages of fixed or of variable length; the printed proof treats
fixed lengths ("a message of the same format and length", p.23). -/
theorem theorem_3_1 (R : Relation) (qw : Polynomial ℕ) (hw : WitnessBound R qw) (pv : Protocol)
    (hpv : pv.IsEfficient) (ε α β : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (L LP : Polynomial ℕ)
    (hL : pv.TranscriptBound R L.eval) (hLP : pv.PerRoundProverBound R LP.eval)
    (hWI : HonestWI pv R ε) (hc : CompleteAt pv R α) :
    (SoundCompAt pv R β →
      IsIODistAIOWF (transcriptValid R qw) (transcriptDomain pv L.eval)
          (transcriptFamily pv L.eval) ∨
        ∀ q : Polynomial ℕ, ∃ pvHat : Protocol,
          IsDetProverCompilation pv pvHat R ε α LP.eval q ∧ SoundCompAt pvHat R β) ∧
    (SoundStatAt pv R β →
      IsIODistAIOWF (transcriptValid R qw) (transcriptDomain pv L.eval)
          (transcriptFamily pv L.eval) ∨
        ∀ q : Polynomial ℕ, ∃ pvHat : Protocol,
          IsDetProverCompilation pv pvHat R ε α LP.eval q ∧ SoundStatAt pvHat R β) := by sorry

end WICanon
