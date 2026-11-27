-- Prove2me | Theorems.Thm_SinkhornHall_Supplement_lemma_1_2
-- name    : SinkhornHall.Supplement.lemma_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:04:43.606804+00:00
-- url     : https://prove2.me/theorems/c16d1bce-1910-4255-90b4-9766b78c0113
-- title:
--   Lemma 1.2 — Pythagorean inequality for the KL divergence of nonnegative vectors
-- statement:
--   Let $\mathcal P\subseteq\mathbb R^n$ be a closed convex set contained in $\{p: \mathbf 1^\top p=C,\ p_i\ge0\ (i\in[n])\}$ for some $C\ge0$, let $r\in\mathbb R^n$ be nonnegative (its sum need not be $C$), and let $p^*\in\mathcal P$ satisfy $D(p^*\|r)=\inf_{p\in\mathcal P}D(p\|r)$, where $D(p\|q)=\sum_ip_i\log(p_i/q_i)$ with $0\log(0/x)=0$ and $x\log(x/0)=+\infty$. Then
--
--   $$D(p\|p^*)+D(p^*\|r)\le D(p\|r)\qquad(\forall p\in\mathcal P).$$
--
--   This is the Pythagorean inequality at an information projection; the paper uses it to turn the rate of Lemma 2.9 into the rate of the row marginals (Lemma 2.13).
--
--   Differences from the source:
--   - encoding: $D$ with values in $[-\infty,\infty]$ → `EReal` (`klDiv`, `matKL`), $\top$ when some $q_i=0<p_i$; reason: the paper's $\infty$ convention, same instances
--   - encoding: "closed (compact)" → `IsClosed P`; reason: a closed subset of the bounded set $\{p\ge0, \mathbf 1^\top p=C\}$ is compact
--   - encoding: index sets $[n]$, $[m]$ → arbitrary finite types `ι`, `κ`; reason: every finite type is in bijection with some $[n]$; the empty types ($n=0$ or $m=0$, outside the paper's convention) only add trivially true or vacuous instances
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Lemma 1.2, p.4 (and the note after it)

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis
import Definitions.Def_SinkhornHall_Supplement_KL

open Finset Filter Topology

namespace SinkhornHall.Supplement

/-- **Lemma 1.2 (Pythagorean theorem for the KL divergence).**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Lemma 1.2, p.4: "Let P be a closed (compact) convex set
in {p ∈ ℝⁿ | 1⊤p = C, p_i ≥ 0 (i ∈ [n])} for some C ≥ 0. For a nonnegative vector r ∈ ℝⁿ, let
p* ∈ P satisfy D(p*‖r) = inf_{p∈P} D(p‖r). Then it holds D(p‖p*) + D(p*‖r) ≤ D(p‖r) (∀p ∈ P)."
The note after it (p.4) says the sum of `r` need not be `C`.

**Formalization Note.** `D` is `klDiv` in `EReal` (`⊤` allowed, including for the infimum).
"Closed (compact)" is `IsClosed P`; a closed subset of the simplex-like set is compact. The index
set is any finite type. -/
theorem lemma_1_2 {ι : Type*} [Fintype ι] (C : ℝ) (hC : 0 ≤ C) (P : Set (ι → ℝ))
    (hPclosed : IsClosed P) (hPconv : Convex ℝ P)
    (hPsub : P ⊆ {p | ∑ i, p i = C ∧ ∀ i, 0 ≤ p i}) (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i)
    (pstar : ι → ℝ) (hpstar : pstar ∈ P)
    (hmin : SinkhornHall.klDiv pstar r = ⨅ p ∈ P, SinkhornHall.klDiv p r) :
    ∀ p ∈ P,
      SinkhornHall.klDiv p pstar + SinkhornHall.klDiv pstar r ≤ SinkhornHall.klDiv p r := by sorry

end SinkhornHall.Supplement
