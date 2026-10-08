-- Prove2me | Theorems.Thm_Supermodularity_Games_exists_monotone_greatest_least_equilibrium_v2
-- name    : Supermodularity.Games.exists_monotone_greatest_least_equilibrium_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:54.339119+00:00
-- url     : https://prove2.me/theorems/801ced4d-0c16-4e12-a174-335c06cea8c6
-- title:
--   Theorem 4.2.2 - the greatest and least equilibrium points increase with a parameter (corrected: supermodularity and increasing differences on the union of the strategy sets)
-- statement:
--   Let $T$ be a partially ordered set and, for each $t \in T$, let $(N, S^t, \{f_i^t\}_{i\in N})$ be a noncooperative game with the same finite nonempty set of players $N$, strategies of player $i$ in $\mathbb{R}^{m_i}$, feasible joint strategy set $S^t \subseteq \mathbb{R}^m$ ($m = \sum_i m_i$) and payoff functions $f_i^t$. Write $S^t_i$ and $S^t_{-i}$ for the projections of $S^t$ onto player $i$'s and onto the other players' strategies, and $S^t_i(x_{-i})$ for the feasible section. Assume:
--
--   1. for each $t$, $(N, S^t, \{f_i^t\})$ is a **supermodular game**: $S^t$ is a sublattice of $\mathbb{R}^m$, $f_i^t(y_i, x_{-i})$ is supermodular in $y_i$ on $S^t_i$ for each $x_{-i} \in S^t_{-i}$, and $f_i^t(y_i, x_{-i})$ has increasing differences in $(y_i, x_{-i})$ on $S^t_i \times S^t_{-i}$, for each $i$;
--   2. (**correction**) for each $t$ and $i$, $f_i^t(y_i, x_{-i})$ is supermodular in $y_i$ on $\bigcup_{s\in T} S^s_i$ for each $x_{-i} \in \bigcup_{s\in T} S^s_{-i}$, and has increasing differences in $(y_i, x_{-i})$ on $\big(\bigcup_{s\in T} S^s_i\big) \times \big(\bigcup_{s\in T} S^s_{-i}\big)$;
--   3. $S^t$ is nonempty and compact for each $t$, and $S^t$ is increasing in $t$ on $T$ in the induced set order $\sqsubseteq$;
--   4. $f_i^t(y_i, x_{-i})$ is upper semicontinuous in $y_i$ on $S^t_i(x_{-i})$ for each $x_{-i} \in S^t_{-i}$, each $i$ and each $t$;
--   5. $f_i^t(y_i, x_{-i})$ has increasing differences in $(y_i, t)$ on $\big(\bigcup_{t\in T} S^t_i\big) \times T$ for each $x_{-i} \in \bigcup_{t\in T} S^t_{-i}$ and each $i$.
--
--   Then for every $t \in T$ there exist a greatest equilibrium point $g(t)$ and a least equilibrium point $l(t)$ of the game $(N, S^t, \{f_i^t\})$, and $g$ and $l$ are increasing functions of $t$ on $T$.
--
--   This is Theorem 4.2.2 (Topkis 1979; Milgrom and Roberts 1990a; Sobel 1988), with the hypotheses the proof uses: Theorem 2.8.x gives that the best joint response $Y(x,t)$ is increasing in $(x,t)$, and Theorem 2.5.2 (the parametric fixed-point theorem) gives the greatest and least fixed points and their monotonicity in $t$.
--
--   **Formalization Note.** The retired version transcribed the printed hypotheses of Theorem 4.2.2 literally and was disproved: when supermodularity in $y_i$ and increasing differences in $(y_i, x_{-i})$ are required only on each game's own strategy set $S^t$, a one-player example with chain strategy sets $S^{t} = [0,1]\times\{t\}$ (on which supermodularity is vacuous) has a unique equilibrium that *decreases* in $t$. The printed statement is therefore false as stated; the step of the proof that compares a $t'$-best response with a $t''$-best response (monotonicity of $Y_i(x_{-i}, t)$ in $(x_{-i}, t)$) uses supermodularity in $y_i$ at a pair $y' \in S^{t'}_i$, $y'' \in S^{t''}_i$ and increasing differences in $(y_i, x_{-i})$ between $x'_{-i} \in S^{t'}_{-i}$ and $x''_{-i} \in S^{t''}_{-i}$, i.e. on the unions of item 2. Supermodularity on the union alone would not suffice: a two-player variant of the counterexample (one-dimensional strategies, so supermodularity is automatic; $f_1^{\mathrm{false}}(y,z) = y - 10yz$, $f_1^{\mathrm{true}}(y,z) = 2y - 3yz$, player 2's strategy forced to $z = t$) satisfies everything except the cross-parameter increasing differences in $(y_1, z)$ and again has a decreasing unique equilibrium. Item 2 is exactly the strengthening the proof needs, and it is automatic when the strategy sets do not depend on $t$ (Milgrom–Roberts 1990a, Theorem 6). Also explicit: the set of players is nonempty (the chapter's standing convention); upper semicontinuity is stated for every reference profile $x$, which is the book's condition because the section $\{y_i : (y_i, x_{-i}) \in S^t\}$ is empty unless $x_{-i} \in S^t_{-i}$; compactness is in the product topology of $\mathbb{R}^m$; and, as in the retired version, the greatest and least equilibria are packaged as functions $g, l : T \to \mathbb{R}^m$ since each is unique.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 1998 (reprint 2011), p. 183-184, Theorem 4.2.2 — corrected statement: supermodularity in y_i and increasing differences in (y_i, x_{-i}) are required on ⋃_t S^t_i and (⋃_t S^t_i) × (⋃_t S^t_{-i}), as the proof uses, not only on each S^t

import Mathlib
import Definitions.Def_Supermodularity_Games_IsSupermodularGame
import Definitions.Def_Supermodularity_Games_IsEquilibrium
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder

namespace Supermodularity.Games

/-- Theorem 4.2.2 (Topkis, *Supermodularity and Complementarity*, p. 183–184), corrected.
`T` is a partially ordered set and, for each `t`, `(N, S t, f t)` is a supermodular game with
`S t` nonempty, compact and increasing in `t` (induced set order), payoffs upper
semicontinuous in the player's own strategy on the feasible section, and increasing
differences in `(yᵢ, t)` on `(⋃ₜ Sᵗᵢ) × T` for every `x₋ᵢ ∈ ⋃ₜ Sᵗ₋ᵢ`. Then every game `t` has a
greatest and a least equilibrium point, and both are increasing in `t`.

**Correction to the printed statement.** As printed, the book only asks each game `t` to be
supermodular on its own strategy set `S t`; but the comparative-statics step of the proof
(monotonicity of the best joint response `Y(x, t)` in `(x, t)`, via Theorem 2.8.x) compares a
`t`-best response with a `t'`-best response and needs supermodularity of `yᵢ ↦ fᵢᵗ(yᵢ, x₋ᵢ)` and
increasing differences in `(yᵢ, x₋ᵢ)` on the union `⋃ₛ Sˢᵢ` (resp. `(⋃ₛ Sˢᵢ) × (⋃ₛ Sˢ₋ᵢ)`) of the
strategy sets across all parameters. With the per-`t` hypotheses alone the conclusion is false
(the accepted disproof of the retired version is a one-player counterexample, and a two-player
variant defeats the supermodularity-only strengthening). The two hypotheses `hsuper_union`
and `hdiff_union` state exactly the conditions the proof uses; they are automatic when the
strategy sets do not depend on `t` (Milgrom–Roberts 1990, Theorem 6). -/
theorem exists_monotone_greatest_least_equilibrium_v2 {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {m : ι → ℕ} {T : Type*} [PartialOrder T]
    (S : T → Set (∀ i, Fin (m i) → ℝ)) (f : T → ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (hgame : ∀ t, IsSupermodularGame (S t) (f t))
    (hsuper_union : ∀ t i, ∀ x ∈ (⋃ s : T, projOthers (S s) i),
      Supermodularity.Monotonicity.SupermodularOn
        (fun y : Fin (m i) → ℝ => f t i (Function.update x i y)) (⋃ s : T, proj (S s) i))
    (hdiff_union : ∀ t i,
      Supermodularity.Monotonicity.IncreasingDifferencesOn
        (fun (y : Fin (m i) → ℝ) (x : ∀ i, Fin (m i) → ℝ) => f t i (Function.update x i y))
        ((⋃ s : T, proj (S s) i) ×ˢ (⋃ s : T, projOthers (S s) i)))
    (hSne : ∀ t, (S t).Nonempty) (hScompact : ∀ t, IsCompact (S t))
    (hSinc : ∀ ⦃t t' : T⦄, t ≤ t' →
      Supermodularity.Lattices.InducedSetOrder (S t) (S t'))
    (husc : ∀ t i (x : ∀ i, Fin (m i) → ℝ),
      UpperSemicontinuousOn (fun y : Fin (m i) → ℝ => f t i (Function.update x i y))
        {y : Fin (m i) → ℝ | Function.update x i y ∈ S t})
    (hdiff : ∀ i, ∀ x ∈ (⋃ t : T, projOthers (S t) i),
      Supermodularity.Monotonicity.IncreasingDifferencesOn
        (fun (y : Fin (m i) → ℝ) (t : T) => f t i (Function.update x i y))
        ((⋃ t : T, proj (S t) i) ×ˢ (Set.univ : Set T))) :
    ∃ g l : T → (∀ i, Fin (m i) → ℝ),
      (∀ t, IsGreatest {x' : ∀ i, Fin (m i) → ℝ | IsEquilibrium (S t) (f t) x'} (g t)) ∧
      (∀ t, IsLeast {x' : ∀ i, Fin (m i) → ℝ | IsEquilibrium (S t) (f t) x'} (l t)) ∧
      Monotone g ∧ Monotone l := by sorry

end Supermodularity.Games
