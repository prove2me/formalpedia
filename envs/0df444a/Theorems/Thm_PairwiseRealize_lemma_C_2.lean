-- Prove2me | Theorems.Thm_PairwiseRealize_lemma_C_2
-- name    : PairwiseRealize.lemma_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:55:41.546336+00:00
-- url     : https://prove2.me/theorems/009253db-1ce3-4d67-b9a4-f528acd36db9
-- title:
--   Lemma C.2, p.16 — the potential never increases and every weight stays below one
-- statement:
--   Let $16\le s\le m$ and $A\in\{0,1\}^{m\times s}$. For every run $(x^{(t)},w^{(t)})_{t\le T}$ of the partial coloring, $\Phi(w^{(t+1)})\le\Phi(w^{(t)})$ for all $t<T$, and $w_i^{(t)}<1$ for all $t\le T$ and every normal $i$.
--
--   The second claim is the one the displacement bound of Lemma C.3 rests on.
--
--   Differences from the source:
--   - generalization: the partial coloring with rational start, direction and weights → every run of the §C.1 step specification, over the reals; reason: the rational implementation of §C.2 is one such run
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), Lemma C.2, p.16 (PDF p.17); §C.1, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_PairwiseRealize_PartialColoring

namespace PairwiseRealize

open PartialColoring

/-- **Lemma C.2, p.16 (PDF p.17).** K. Shi, H. Sun, *Robust Exact Realization of Pairwise Boolean
Statistics*, STOC 2027 submission (manuscript sha256 62090516…): "Lemma C.2. The potential never
increases and every weight stays below one." The procedure is the partial coloring of §C.1
(p.15): `m` binary rows, `s` active variables, `16 ≤ s ≤ m`.

For every `0/1` matrix `A ∈ {0,1}^{m×s}` with `16 ≤ s ≤ m` and every run `(x(t), w(t))_{t ≤ T}` of the
partial coloring, `Φ(w(t+1)) ≤ Φ(w(t))` for every `t < T`, and `wᵢ(t) < 1` for every `t ≤ T` and
every normal `i`.

**Formalization Note** A run is any sequence of states satisfying the §C.1 step specification
(`PartialColoring.IsRun`), which contains the paper's rational implementation of §C.2; the lemma is
stated for all of them. -/
theorem lemma_C_2 (m s : ℕ) (hs : 16 ≤ s) (hsm : s ≤ m) (A : Fin m → Fin s → Bool) (T : ℕ)
    (x : Fin (T + 1) → Fin s → ℝ) (w : Fin (T + 1) → Fin m × Bool → ℝ) (hrun : IsRun A T x w) :
    (∀ t : Fin T, Phi (w t.succ) ≤ Phi (w t.castSucc)) ∧ ∀ t i, w t i < 1 := by sorry

end PairwiseRealize
