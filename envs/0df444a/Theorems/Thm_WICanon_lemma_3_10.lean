-- Prove2me | Theorems.Thm_WICanon_lemma_3_10
-- name    : WICanon.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:05:27.60166+00:00
-- url     : https://prove2.me/theorems/abb9a6cf-8e34-4a4a-a8c9-3d9acde78b46
-- title:
--   Lemma 3.10 — from computational to statistical WI
-- statement:
--   Let $(P,V)$ be a computational honest-verifier $\epsilon$-WI protocol for $\mathcal R$ with an efficient prover (given a witness), and let $\ell(n)$ bound the transcript length. Consider the family, for $a=(x,w_0,w_1)$ with $(x,w_0),(x,w_1)\in\mathcal R_n$,
--
--   $$f_a(i,b,r_P,r_V)=\langle P(x,w_b;r_P),V(x;r_V)\rangle_{\le i}.$$
--
--   If $\{f_a\}$ is not an infinitely-often distributional auxiliary-input one-way function, then $(P,V)$ is honest-verifier $\epsilon'$-SWI for $\epsilon'=\epsilon+\mathrm{negl}$.
--
--   Without such functions, computational indistinguishability of the two transcript distributions is already statistical.
--
--   **Formalization Note** One negligible function is chosen before $x$.
--
--   Differences from the source:
--   - reading: for every x, w0, w1 and every non-uniform PPT D: advantage < δ(|x|) → each D is bound from some length on; reason: the literal order lets D depend on x, and a table in the finite control collapses WI to SWI at every x; the reading is a weaker hypothesis
--   - encoding: non-uniform D with advice z_n on inputs of length n → advice and 1^n indexed by n = |x|; reason: |x| is the security parameter of the notion; the view determines no input length in general
--   - reading: relation R → R with a polynomial witness bound; reason: the index a = (x, w0, w1) in {0,1}^m(n) and the PPT prover presuppose it
--   - encoding: states st_V,i, st_P,i and per-round coins → next-message functions of the history, one coin tape per party; reason: a state is computed from the coins and the messages; same protocols
--   - encoding: prover coins polynomial in |x| + |w| → a coin count depending on |x|; reason: witnesses are polynomially bounded and a machine may ignore coins
--   - reading: f_a on a = (x, w0, w1) with both pairs in R_n, existence of a in {0,1}^m(n) → an index set of valid a, padded with empty components of the tuple code; reason: Theorem 3.1 and Lemma 3.10 define f_a only there
--   - reading: codomain {0,1}^m(n) in Definition 2.6 → free codomain; reason: Theorem 3.1's family outputs prefixes of varying length and Theorem 3.7's has codomain {0,1}^ℓ(n)
--   - reading: index i uniform in [ℓ] → i = min(val(s) + 1, L) for s uniform in {0,1}^⌈log₂ L⌉; reason: the input of a family is a uniform bit string; each value keeps probability at least 1/(2L)
--   - encoding: first i bits of the transcript → first i bits of the transcript written with the tuple code; reason: a fixed injective encoding, needed for messages of varying length
--   - encoding: A(a, y) → A(1^n, a, y); reason: |a| ≥ 2n for this family, so 1^n adds no power
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Lemma 3.10, p.22 (restated as Lemma B.3, p.46)

import Mathlib
import Definitions.Def_OWFLocalDesc_Negligible
import Definitions.Def_WICanon_IsNPRelation
import Definitions.Def_WICanon_ProtocolProps
import Definitions.Def_WICanon_WitnessIndist
import Definitions.Def_WICanon_DistAIOWF
import Definitions.Def_WICanon_TranscriptFamily

set_option autoImplicit false

namespace WICanon

open OWFLocalDesc

/-- **Lemma 3.10** (from computational to statistical WI; restated as Lemma B.3, p.46). Arnon, Mazor,
Pass, Silbak, *Does Witness Indistinguishability Require Cryptography?*, STOC 2027 submission manuscript
(sha256 3f78ec3d…), p.22. If `(P, V)` is computational honest-verifier `ε`-WI for `R` with an efficient
prover, and the transcript family is not an infinitely-often distributional AI-OWF, then `(P, V)` is
honest-verifier `ε′`-SWI for `ε′ = ε + negl`.

**Formalization Note.** `ν` is one negligible function, chosen before `x`. `HonestWI` is the asymptotic
reading of Definition 2.9; the literal one would make this lemma contentless. Witnesses are polynomially
bounded since `a = (x, w_0, w_1)` lies in `{0,1}^{m(n)}`. -/
theorem lemma_3_10 (R : Relation) (q : Polynomial ℕ) (hw : WitnessBound R q) (pv : Protocol)
    (hpv : pv.IsEfficient) (ε : ℕ → ℝ) (hWI : HonestWI pv R ε) (L : Polynomial ℕ)
    (hL : pv.TranscriptBound R L.eval)
    (hnot : ¬ IsIODistAIOWF (transcriptValid R q) (transcriptDomain pv L.eval)
      (transcriptFamily pv L.eval)) :
    ∃ ν : ℕ → ℝ, Negligible ν ∧ HonestSWI pv R (fun n => ε n + ν n) := by sorry

end WICanon
