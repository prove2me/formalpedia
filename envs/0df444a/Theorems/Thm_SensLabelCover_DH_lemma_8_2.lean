-- Prove2me | Theorems.Thm_SensLabelCover_DH_lemma_8_2
-- name    : SensLabelCover.DH.lemma_8_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:34:38.893897+00:00
-- url     : https://prove2.me/theorems/14dc9e6a-c2f6-4416-997d-5b9598c775e8
-- title:
--   Lemma 8.2 — constraint groups from expander walks: $r=1+\lceil(2/\eta)\log(8/p)\rceil$, $M=|E|p^{-O_\eta(1)}$, each index in at most $rM/|E|$ groups, dense sets missed by at most a $p/8$ fraction
-- statement:
--   For every $0<\eta<1/2$ there is a constant $C_\eta>0$ such that the following holds. Let $E$ be a nonempty finite set and $0<p\le1/4$, and put $r=1+\lceil(2/\eta)\log(8/p)\rceil$ (natural logarithm). There is a list of ordered groups $S_1,\dots,S_M\in E^r$, repetitions allowed, with $1\le M\le|E|\,p^{-C_\eta}$, such that every $e\in E$ belongs to at most $rM/|E|$ of the groups and, for every $W\subseteq E$ with $|W|\ge\eta|E|$,
--   $$\Pr_{j\in[M]}\big[S_j\text{ contains no member of }W\big]\le p/8 .$$
--   The list depends only on $E$, $\eta$ and $p$.
--
--   The groups let a few tests detect any assignment that violates a constant fraction of constraints, while each constraint affects few tests.
--
--   Differences from the source:
--   - reading: $M=|E|p^{-O_\eta(1)}$ → $1\le M\le|E|p^{-C_\eta}$ with $C_\eta>0$ fixed by $\eta$ before $E$ and $p$; reason: $O_\eta(1)$ is an upper bound by a constant depending only on $\eta$, and the uniform $j\in[M]$ needs $M\ge1$.
--   - encoding: groups $S_j\in E^r$, $j\in[M]$ → `S : Fin M → Fin r → E`; "belongs to" → some coordinate equals $e$; $\Pr_j$ → count divided by $M$; reason: Lean convention, same instances.
-- source:
--   Fleming, Hopkins, Yoshida, Sensitivity and Locality Lower Bounds via Low-Soundness Label Cover, STOC 2027 submission (manuscript sha256 5bfe95ad…), p. 42 (PDF 45), Lemma 8.2

import Mathlib

namespace SensLabelCover.DH

/-- Lemma 8.2 (Constraint groups from expander walks), p. 42 (PDF p. 45). `O_η(1)` is a
constant `C_η` depending only on `η`; `log` is natural. Groups are `S j : Fin r → E`
(`j ∈ [M]` is `j : Fin M`). -/
theorem lemma_8_2 :
    ∀ η : ℝ, 0 < η → η < 1 / 2 → ∃ Cη : ℝ, 0 < Cη ∧
      ∀ (E : Type) [Fintype E] [DecidableEq E] [Nonempty E] (p : ℝ), 0 < p → p ≤ 1 / 4 →
        ∃ (M : ℕ) (S : Fin M → Fin (1 + ⌈(2 / η) * Real.log (8 / p)⌉₊) → E),
          0 < M ∧ (M : ℝ) ≤ (Fintype.card E : ℝ) * p ^ (-Cη) ∧
          (∀ e : E, ((Finset.univ.filter (fun j => ∃ t, S j t = e)).card : ℝ) ≤
            ((1 + ⌈(2 / η) * Real.log (8 / p)⌉₊ : ℕ) : ℝ) * M / Fintype.card E) ∧
          ∀ W : Finset E, η * (Fintype.card E : ℝ) ≤ W.card →
            ((Finset.univ.filter (fun j => ∀ t, S j t ∉ W)).card : ℝ) / M ≤ p / 8 := by sorry

end SensLabelCover.DH
