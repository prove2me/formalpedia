-- Prove2me | Theorems.Thm_SparseSDP_TwoSided_corollary_2_6
-- name    : SparseSDP.TwoSided.corollary_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:55:27.570979+00:00
-- url     : https://prove2.me/theorems/3f6202fe-b597-4876-8f9c-151786d8a107
-- title:
--   Corollary 2.6, p. 21 — the gapped binary search recovers an approximate SDP solution
-- statement:
--   Fix $\eta,\xi,\zeta>0$, a normalized instance with $|b_j|\le R$, $R,r\ge1$, and strong duality within the radii. Run the gapped binary search. Suppose that every queried target-value game is solved to saddle-point gap at most $\xi$ and that every computed upper certificate satisfies $u_g-\zeta\le\tilde u_g\le u_g$. Then the search makes at most $1+\max\{0,\lceil\log_2(2R/\eta)\rceil\}$ game solves and returns $\hat g$ with its matrix $\hat X\succeq0$, $\operatorname{Tr}\hat X\le R$, such that
--   $$
--   \mathrm{OPT}-\eta\le\hat g\le\mathrm{OPT}+(1+r)(\xi+\zeta),
--   $$
--   and
--   $$
--   \langle C,\hat X\rangle\ge\mathrm{OPT}-\eta-\xi-\zeta,\qquad\langle A_j,\hat X\rangle\le b_j+\xi+\zeta\quad\forall j.
--   $$
--
--   This reduces the SDP to logarithmically many games.
--
--   Differences from the source:
--   - reading: $O(\log(2+R/\eta))$ game solves → the exact bound $1+\max\{0,\lceil\log_2(2R/\eta)\rceil\}$; reason: that is the bound the proof derives on p. 22
--   - reading: its associated matrix $\hat X$ → the leading block of the retained $Y$; reason: Proposition 2.4, item 2, as the proof applies it
--   - generalization: the game solver and certificate of §2.6, over the data of §2.6 → abstract charged procedures and any `RCLike` field, with assumptions only at the queries of the run; reason: it specializes to the solver's procedures on the real instance
--   - encoding: $j\in[m]$ ranging over the constraints → `Normalized` includes $1\le m$; reason: a nondegeneracy condition that only excludes an undefined case: the page's $\min_{j\in[m]}$ and the $\log(2m)$, $\log(16mn/\delta)$ of Algorithm 7 presuppose $m\ge1$
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Corollary 2.6, p. 21, Eqs. (72), (73); query bound p. 22

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_Dall
import Definitions.Def_SparseSDP_TwoSided_gappedSearch

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace SparseSDP.TwoSided

/-- **Corollary 2.6** (Recovering an Approximate SDP Solution), p. 21, with the query bound of its
proof, p. 22.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Corollary 2.6, p. 21.

`solve` and `cert` are abstract charged procedures; `Yof`, `pof` read a returned solution as a pair
in `RS_{n+1} × ∆_{m+1}`. The assumption is made only at the queries of this run: every queried game
is solved to gap at most `ξ` and every computed certificate satisfies Eq. (66). -/
theorem corollary_2_6 {𝕜 : Type*} [RCLike 𝕜] [DecidableEq 𝕜] {n m s : ℕ} {σ : Type}
    (I : Instance 𝕜 n m)
    (solve : ℝ → Prog σ) (cert : ℝ → σ → Prog ℝ)
    (Yof : σ → Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) 𝕜) (pof : σ → Fin (m + 1) → ℝ)
    (R r η ξ ζ OPT : ℝ) (tape : Tape)
    (hI : I.Normalized s) (hR : 1 ≤ R) (hr : 1 ≤ r) (hb : ∀ j, |I.b j| ≤ R)
    (hSD : StrongDuality I R r OPT) (hη : 0 < η) (hξ : 0 < ξ) (hζ : 0 < ζ)
    (hq : ∀ q ∈ (runVal (gappedSearch solve cert R η ζ) tape).queries,
      Yof q.sol ∈ (Spect R : Set (Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) 𝕜)) ∧
      pof q.sol ∈ Simplex (m + 1) 1 ∧
      gap (Dall I R q.g) R 1 (Yof q.sol) (pof q.sol) ≤ ξ ∧
      upCert I R q.g (pof q.sol) - ζ ≤ q.cert ∧ q.cert ≤ upCert I R q.g (pof q.sol)) :
    (runVal (gappedSearch solve cert R η ζ) tape).queries.length ≤ searchBudget R η ∧
    OPT - η ≤ (runVal (gappedSearch solve cert R η ζ) tape).ghat ∧
    (runVal (gappedSearch solve cert R η ζ) tape).ghat ≤ OPT + (1 + r) * (ξ + ζ) ∧
    (Yof (runVal (gappedSearch solve cert R η ζ) tape).sol).toBlocks₁₁.PosSemidef ∧
    RCLike.re (Matrix.trace (Yof (runVal (gappedSearch solve cert R η ζ) tape).sol).toBlocks₁₁) ≤ R ∧
    OPT - η - ξ - ζ ≤
      hs I.C (Yof (runVal (gappedSearch solve cert R η ζ) tape).sol).toBlocks₁₁ ∧
    ∀ j, hs (I.A j) (Yof (runVal (gappedSearch solve cert R η ζ) tape).sol).toBlocks₁₁ ≤
      I.b j + ξ + ζ := by sorry

end SparseSDP.TwoSided
