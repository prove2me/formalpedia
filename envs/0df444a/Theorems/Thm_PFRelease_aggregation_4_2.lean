-- Prove2me | Theorems.Thm_PFRelease_aggregation_4_2
-- name    : PFRelease.aggregation_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:22.527578+00:00
-- url     : https://prove2.me/theorems/a790df44-c1bc-49bc-97cf-3b17dd7634b0
-- title:
--   §4.2 aggregation step — $\nu$ friendly blocks give score $(\nu/m)\tau'$ against the whole dataset
-- statement:
--   Let $\varphi$ be a concave friendliness score, $x$ a non-null record, and $s$ a dataset of $n=mb$ slots ($b>0$) split into $m$ blocks $s^{(1)},\dots,s^{(m)}$ of $b$ slots each. If $\nu$ of the blocks satisfy $\varphi(s^{(j)},x)\ge\tau'$, then
--   $$
--   \varphi(s,x)\ \ge\ \frac{\nu}{m}\,\tau' .
--   $$
--
--   This is the aggregation step of the proof of Theorem 4.5: a record friendly at level $2\tau$ with at least half of the intact blocks is $\tau$-friendly with the whole filtered dataset.
--
--   **Formalization Note** The blocks are those of an equipartition $\pi$ of the $mb$ slots, each listed in index order; the $\nu$ blocks are an arbitrary set $S$ of block labels with $\nu=|S|$.
--
--   Differences from the source:
--   - encoding: the $m$ equal-size blocks of a dataset → the blocks of an equipartition $\pi$ of $mb$ slots into $m$ blocks of size $b>0$, each in index order; reason: by permutation invariance the order inside a block and the labelling of blocks do not matter
--   - generalization: a threshold $\tau'$ (a real number) → $\tau'\in[0,\infty]$; reason: scores take values in $[0,\infty]$; a real $\tau'\ge0$ is a special case, and for $\tau'<0$ the bound is trivial
--   - reading: the record $x$ of the passage → a non-null record, `x ≠ none`; reason: Definition 4.4 gives permutation invariance and concavity only at non-null records and leaves the values at $\perp$ unrestricted, so the passage can only mean non-null $x$, the case of its use in the proof of Theorem 4.5
--   - encoding: datasets $s\in\mathcal X^n$ with null record $\perp$, slots $1,\dots,n$ → `Fin n → Option X` with `none` $=\perp$, slots $0,\dots,n-1$; reason: same objects
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), §4.2, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_PFRelease_Dataset
import Definitions.Def_PFRelease_IsScore
import Definitions.Def_PFRelease_IsConcave
import Definitions.Def_PFRelease_filterLaw

namespace PFRelease

/-- **Aggregation step (§4.2)** (Shenfeld, Tsfadia, Ligett, *Propose-Filter-Release: Scaling Noise to Typical Sensitivity via
Private Filtering*, arXiv:2610.40654 (held version, sha256 e1d516b3…), §4.2, p.13 = PDF p.15). If `ν` of the `m` equal-size
blocks of a dataset satisfy `φ(s^{(j)}, x) ≥ τ′`, then permutation invariance, repeated concavity and
`φ ≥ 0` on the remaining blocks give the lower bound `(ν/m)τ′` on the score against the whole
dataset.

**Formalization Note** The dataset has `n = m·b` slots (`b > 0`), split by an equipartition
`π` into `m` blocks of `b` slots, each block listed in index order (`block`). `ν = |S|` for an
arbitrary set `S` of blocks on which the score is at least `τ′`; scores and `τ′` are in `[0, ∞]`
(a real `τ′ ≥ 0` is `ENNReal.ofReal τ′`; for `τ′ < 0` the claim is trivial). The record `x` is
non-null, where score axioms apply. -/
theorem aggregation_4_2 {X : Type*} (φ : List (Option X) → Option X → ENNReal) (hφ : IsScore φ)
    (hconc : IsConcave φ) (m b : ℕ) (hb : 0 < b) (π : Fin (m * b) → Fin m)
    (hπ : IsEquipartition b π) (s : Fin (m * b) → Option X) (x : Option X) (hx : x ≠ none)
    (τ' : ENNReal) (S : Finset (Fin m)) (hS : ∀ j ∈ S, τ' ≤ φ (block π s j) x) :
    ((S.card : ENNReal) / (m : ENNReal)) * τ' ≤ φ (toList s) x := by sorry

end PFRelease
