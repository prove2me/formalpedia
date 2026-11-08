-- Prove2me | Theorems.Thm_WICanon_theorem_3_7
-- name    : WICanon.theorem_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:06:28.287045+00:00
-- url     : https://prove2.me/theorems/d6eb10ed-0c57-4555-87ec-0714e4852129
-- title:
--   Theorem 3.7 ([IL89]) — distributional inversion yields next-bit predictors
-- statement:
--   Let $\{f_a:\{0,1\}^{m(n)}\to\{0,1\}^{\ell(n)}\}_{a\in\{0,1\}^{\lambda(n)}}$ be an efficiently computable family and let $f'_a(i,x)=f_a(x)_{\le i}$ for $i\in[\ell(n)]$. If $\{f'_a\}$ is not an infinitely-often distributional one-way function, then for any $\mu\in1/\mathrm{poly}$ there is a $\mu$-next-bit predictor for the collection $\{f_a(X_n)\}_{a,n}$, where $X_n$ is uniform on $\{0,1\}^{m(n)}$.
--
--   This is the link between the absence of one-way functions and next-bit prediction, due to Impagliazzo and Luby.
--
--   **Formalization Note** The theorem is stated over a set of valid indices, which the proof of Theorem 3.1 needs for $a=(x,w,w)$. The printed one is the case in which every string of length $\lambda(n)$ is valid.
--
--   Differences from the source:
--   - generalization: all a ∈ {0,1}^λ(n) → any index set valid of strings of length λ(n); reason: every string of length λ(n) being valid is the printed theorem; Theorem 3.1 needs a = (x, w, w)
--   - reading: codomain {0,1}^m(n) in Definition 2.6 → free codomain; reason: Theorem 3.1's family outputs prefixes of varying length and Theorem 3.7's has codomain {0,1}^ℓ(n)
--   - reading: index i uniform in [ℓ] → i = min(val(s) + 1, L) for s uniform in {0,1}^⌈log₂ L⌉; reason: the input of a family is a uniform bit string; each value keeps probability at least 1/(2L)
--   - encoding: Pred with binary-fraction outputs and runtime q(n) → a polynomial-time machine whose output string is read as a binary fraction capped at 1; reason: a polynomial-time machine on polynomially long inputs has such a q
--   - encoding: for every sequence {a_n} and every sufficiently large n → a threshold uniform in a; reason: a sequence of bad indices at growing n would contradict the sequence form
--   - generalization: ε ∈ 1/poly → ε(n) ≥ 1/p(n) with no upper bound; reason: it contains every 1/p
--   - encoding: A(a, y) → A(1^n, a, y); reason: the inverter of the negated hypothesis may also read 1^n; n is polynomially readable from the lengths when the family is nontrivial
--   - encoding: efficiently computable family indexed by a → one machine on (1^n, a, x); reason: when λ and m are both constant the family is trivially invertible, otherwise n is polynomially readable from the lengths
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Theorem 3.7, p.21

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_WICanon_Law
import Definitions.Def_WICanon_PolyBounds
import Definitions.Def_WICanon_AIOWF
import Definitions.Def_WICanon_DistAIOWF
import Definitions.Def_WICanon_TranscriptFamily
import Definitions.Def_WICanon_NextBit

set_option autoImplicit false

namespace WICanon

open QAlgorithms.Complexity

/-- **Theorem 3.7** ([IL89]; distributional AI-OWF and next-bit predictor). Arnon, Mazor, Pass, Silbak,
*Does Witness Indistinguishability Require Cryptography?*, STOC 2027 submission manuscript (sha256
3f78ec3d…), p.21. For an efficiently computable family `f_a : {0,1}^{m(n)} → {0,1}^{L(n)}` with
`f'_a(i, x) := f_a(x)_{≤i}`: if `{f'_a}` is not an infinitely-often distributional one-way function, then
for any `μ ∈ 1/poly` there is a `μ`-next-bit predictor for the collection `{f_a(X_n)}`.

**Formalization Note.** Stated over an arbitrary index set `valid` of strings of length `λ(n)`; the
printed theorem is the case `valid n a := |a| = λ(n)`. Theorem 3.1 applies it to `a = (x, w, w)`. -/
theorem theorem_3_7 (valid : ℕ → Str → Prop) (lam : Polynomial ℕ) (m L : ℕ → ℕ)
    (hm : IsPolyLen m) (hL : IsPolyLen L) (f : ℕ → Str → Str → Str)
    (hf : EfficientOn valid m f) (hlam : ∀ n a, valid n a → a.length = lam.eval n)
    (hlen : ∀ n a x, valid n a → x.length = m n → (f n a x).length = L n)
    (hnot : ¬ IsIODistAIOWF valid (prefixDomain L m) (prefixFamily L f))
    (μ : ℕ → ℝ) (hμ : InvPoly μ) :
    ∃ M : PredictorMachine,
      IsCollectionPredictor valid L (fun n a => coinLaw (m n) (f n a)) M μ := by sorry

end WICanon
